#!/usr/bin/env bash
# Pre-commit summary: build, count sorry declarations, and report diff of sorry/axiom changes.
# Tracks footprint of unproven lemmas. Adding internal sorries within a lemma that already
# has sorry is OK (splitting goals); this script focuses on declaration-level counts.
#
# Options:
#   -b branchname  Compare current branch to branchname (instead of uncommitted changes)

set -euo pipefail

COMPARE_BRANCH=""
while getopts "b:" opt; do
  case "$opt" in
    b) COMPARE_BRANCH="$OPTARG" ;;
    *) echo "Usage: $0 [-b branchname]"; exit 1 ;;
  esac
done

# Colours (only when stdout is a TTY)
if [[ -t 1 ]]; then
  RED='\033[0;31m'
  GREEN='\033[0;32m'
  YELLOW='\033[1;33m'
  NC='\033[0m'
else
  RED='' GREEN='' YELLOW='' NC=''
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
cd "$ROOT"

if [[ -n "$COMPARE_BRANCH" ]] && ! git rev-parse "$COMPARE_BRANCH" &>/dev/null; then
  echo -e "${RED}Branch '$COMPARE_BRANCH' not found.${NC}"
  exit 1
fi

echo "== Pre-commit summary =="
echo

# --- 1. Lake build and sorry declaration count ---
echo "--- Build ---"
BUILD_LOG=$(mktemp)
trap 'rm -f "$BUILD_LOG"' EXIT

if ! lake build > "$BUILD_LOG" 2>&1; then
  echo -e "${RED}Build failed:${NC}"
  cat "$BUILD_LOG"
  exit 1
fi

# Count warnings (excluding sorry)
ALL_WARNINGS=$(grep -cE "^warning:" "$BUILD_LOG" 2>/dev/null || echo 0)
SORRY_WARNINGS_RAW=$(grep -E "declaration uses 'sorry'" "$BUILD_LOG" 2>/dev/null || true)
SORRY_WARN_COUNT=$(echo "$SORRY_WARNINGS_RAW" | grep -c . 2>/dev/null || echo 0)
OTHER_WARNINGS=$((ALL_WARNINGS - SORRY_WARN_COUNT))
if [[ $OTHER_WARNINGS -gt 0 ]]; then
  echo -e "${YELLOW}Building files emits $OTHER_WARNINGS warnings (excluding sorry).${NC}"
fi

# Count declarations using sorry per file (from "declaration uses 'sorry'" warnings)
echo "Build completed."
echo
echo "--- Lemmas with sorry (from build warnings) ---"
if [[ -z "$SORRY_WARNINGS_RAW" ]]; then
  echo "  (none)"
  echo "  Total: 0"
else
  # Extract file path (e.g. LeanProofs/FaultRobustnessProofs.lean from "warning: LeanProofs/...:LINE:COL: ...")
  echo "$SORRY_WARNINGS_RAW" | sed -nE "s/^warning: ([^:]+):[0-9]+:[0-9]+:.*/\1/p" | sort | uniq -c | sort -rn | while read count file; do
    printf "  %s: %d\n" "$file" "$count"
  done
  echo "  Total: $SORRY_WARN_COUNT"
fi
echo

# --- 2. Git diff: added/removed sorry and axiom ---
if [[ -n "$COMPARE_BRANCH" ]]; then
  echo "--- Git diff: sorry/axiom changes (HEAD vs $COMPARE_BRANCH) ---"
  DIFF=$(git diff "$COMPARE_BRANCH"..HEAD --no-color 2>/dev/null || true)
  if [[ -z "$DIFF" ]]; then
    echo "  No changes since $COMPARE_BRANCH."
    echo "  Added sorry: 0, Removed sorry: 0"
    echo "  Added axiom: 0, Removed axiom: 0"
  else
    DO_DIFF_PARSE=1
  fi
else
  echo "--- Git diff: sorry/axiom changes (vs HEAD) ---"
  DIFF=$(git diff HEAD --no-color 2>/dev/null || true)
  if [[ -z "$DIFF" ]]; then
    echo "  No uncommitted changes."
    echo "  Added sorry: 0, Removed sorry: 0"
    echo "  Added axiom: 0, Removed axiom: 0"
  else
    DO_DIFF_PARSE=1
  fi
fi

if [[ "${DO_DIFF_PARSE:-0}" -eq 1 ]]; then
  # Parse diff: track current file, count +/- lines containing sorry or axiom
  declare -A ADDED_SORRY
  declare -A REMOVED_SORRY
  declare -A ADDED_AXIOM
  declare -A REMOVED_AXIOM
  CURRENT_FILE=""

  while IFS= read -r line; do
    # diff --git can use a/b (standard) or c/w (no-index/work tree)
    if [[ "$line" =~ ^diff\ --git\ [a-z]/(.+)\ [a-z]/ ]]; then
      path="${BASH_REMATCH[1]}"
      [[ "$path" == *.lean ]] && CURRENT_FILE="$path" || CURRENT_FILE=""
    elif [[ -n "$CURRENT_FILE" ]]; then
      if [[ "$line" == +* ]]; then
        added="${line:1}"
        if [[ "$added" == *"sorry"* ]]; then
          ADDED_SORRY["$CURRENT_FILE"]=$((${ADDED_SORRY["$CURRENT_FILE"]:-0} + 1))
        fi
        if [[ "$added" == *"axiom"* ]]; then
          ADDED_AXIOM["$CURRENT_FILE"]=$((${ADDED_AXIOM["$CURRENT_FILE"]:-0} + 1))
        fi
      elif [[ "$line" == -* ]] && [[ "$line" != ---* ]]; then
        removed="${line:1}"
        if [[ "$removed" == *"sorry"* ]]; then
          REMOVED_SORRY["$CURRENT_FILE"]=$((${REMOVED_SORRY["$CURRENT_FILE"]:-0} + 1))
        fi
        if [[ "$removed" == *"axiom"* ]]; then
          REMOVED_AXIOM["$CURRENT_FILE"]=$((${REMOVED_AXIOM["$CURRENT_FILE"]:-0} + 1))
        fi
      fi
    fi
  done <<< "$DIFF"

  TOT_ADD_S=0
  TOT_REM_S=0
  TOT_ADD_A=0
  TOT_REM_A=0

  ALL_FILES=()
  for f in "${!ADDED_SORRY[@]}" "${!REMOVED_SORRY[@]}" "${!ADDED_AXIOM[@]}" "${!REMOVED_AXIOM[@]}"; do
    ALL_FILES+=("$f")
  done
  ALL_FILES=($(printf '%s\n' "${ALL_FILES[@]}" | sort -u))

  for f in "${ALL_FILES[@]}"; do
    as=${ADDED_SORRY["$f"]:-0}
    rs=${REMOVED_SORRY["$f"]:-0}
    aa=${ADDED_AXIOM["$f"]:-0}
    ra=${REMOVED_AXIOM["$f"]:-0}
    if [[ "$as" -gt 0 || "$rs" -gt 0 || "$aa" -gt 0 || "$ra" -gt 0 ]]; then
      echo "  $f:"
      [[ "$as" -gt 0 || "$rs" -gt 0 ]] && echo "    sorry: +$as -$rs"
      [[ "$aa" -gt 0 || "$ra" -gt 0 ]] && echo "    axiom: +$aa -$ra"
      TOT_ADD_S=$((TOT_ADD_S + as))
      TOT_REM_S=$((TOT_REM_S + rs))
      TOT_ADD_A=$((TOT_ADD_A + aa))
      TOT_REM_A=$((TOT_REM_A + ra))
    fi
  done

  if [[ ${#ALL_FILES[@]} -eq 0 ]] || [[ $TOT_ADD_S -eq 0 && $TOT_REM_S -eq 0 && $TOT_ADD_A -eq 0 && $TOT_REM_A -eq 0 ]]; then
    echo "  No sorry/axiom changes in diff."
  fi
  echo
  # Colour sorry/axiom totals: same=default, decrease=green, increase=red
  NET_S=$((TOT_ADD_S - TOT_REM_S))
  NET_A=$((TOT_ADD_A - TOT_REM_A))
  if [[ $NET_S -gt 0 ]]; then C_S="$RED"; elif [[ $NET_S -lt 0 ]]; then C_S="$GREEN"; else C_S="$NC"; fi
  if [[ $NET_A -gt 0 ]]; then C_A="$RED"; elif [[ $NET_A -lt 0 ]]; then C_A="$GREEN"; else C_A="$NC"; fi
  echo -e "  Total: ${C_S}sorry +$TOT_ADD_S -$TOT_REM_S${NC} | ${C_A}axiom +$TOT_ADD_A -$TOT_REM_A${NC}"
fi
echo
echo "Done."
