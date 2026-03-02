#!/usr/bin/env bash
set -u

# Run from project root (derived from script location, no hardcoded paths)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

EXAMPLES_DIR="examples"

TEMP_DIR="testResults"
mkdir -p "$TEMP_DIR"
LOCK_DIR="$TEMP_DIR/.print_lock"

if command -v nproc >/dev/null 2>&1; then
  JOBS=$(nproc)
elif command -v sysctl >/dev/null 2>&1; then
  JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 1)
else
  JOBS=1
fi

print_usage() {
  echo "Usage: $0 [-j|--jobs N] [test]"
  echo "  -j, --jobs N   Number of parallel executions (default: CPU count)"
  echo "  test           Optional test name/path (same as before)"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -j|--jobs)
      JOBS="${2:-}"
      shift 2
      ;;
    -h|--help)
      print_usage
      exit 0
      ;;
    --)
      shift
      break
      ;;
    -*)
      echo "Error: Unknown option '$1'"
      print_usage
      exit 1
      ;;
    *)
      break
      ;;
  esac
done

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "Error: --jobs must be a positive integer"
  exit 1
fi

cleanup() {
  local pids
  pids=$(jobs -pr)
  if [[ -n "$pids" ]]; then
    kill $pids 2>/dev/null || true
  fi
  rm -rf "$TEMP_DIR"
}

trap cleanup EXIT INT TERM

PASS_COUNT=0
FAIL_COUNT=0
FAILED_TESTS=()

run_single_test() {
  local poison_file="$1"
  local base_name
  local result_file
  local report_file
  local status_file
  local expected
  local expect_type
  local exit_code
  local diff_match
  local pass
  local directive_line
  local directive
  local -a extra_args
  local -a directive_args

  base_name=$(basename "$poison_file" .poison)
  result_file="$TEMP_DIR/$base_name.result"
  report_file="$TEMP_DIR/$base_name.report"
  status_file="$TEMP_DIR/$base_name.status"

  if [[ -f "$EXAMPLES_DIR/$base_name.output" ]]; then
    expected="$EXAMPLES_DIR/$base_name.output"
    expect_type="output"
  elif [[ -f "$EXAMPLES_DIR/$base_name.fail" ]]; then
    expected="$EXAMPLES_DIR/$base_name.fail"
    expect_type="fail"
  else
    {
      echo "Skipping $base_name: no .output or .fail"
    } >"$report_file"
    echo "skip" >"$status_file"
    print_report "$report_file"
    return 0
  fi

  extra_args=()
  directive_line=$(head -n1 "$poison_file")
  if [[ "$directive_line" == --!\ * ]]; then
    directive="${directive_line#--!}"
    directive="${directive# }"
    if [[ -n "$directive" ]]; then
      mapfile -t directive_args < <(printf '%s\n' "$directive" | xargs -n1)
      if [[ ${#directive_args[@]} -gt 0 && "${directive_args[0]}" == "poison-interpreter" ]]; then
        directive_args=("${directive_args[@]:1}")
      fi
      extra_args=("${directive_args[@]}")
    fi
  fi

  lake exe poison-interpreter --verbose "${extra_args[@]}" "$poison_file" > "$result_file" 2>&1
  exit_code=$?

  if diff -q "$result_file" "$expected" >/dev/null; then
    diff_match=1
  else
    diff_match=0
  fi

  pass=0
  if [[ $expect_type == "output" && $exit_code -eq 0 && $diff_match -eq 1 ]]; then
    pass=1
  elif [[ $expect_type == "fail" && $exit_code -ne 0 && $diff_match -eq 1 ]]; then
    pass=1
  fi

  if [[ $pass -eq 1 ]]; then
    echo "Passed: $base_name" >"$report_file"
    echo "pass" >"$status_file"
  else
    {
      echo
      echo "Failed: $base_name"
      echo "**************************"
      echo "Expected ($expected):"
      cat "$expected"
      echo
      echo "--------------------------"
      echo
      echo "Actual ($result_file):"
      cat "$result_file"
      echo
      echo "Diff:"
      diff -u "$expected" "$result_file" || true
      echo "**************************"
    } >"$report_file"
    echo "fail" >"$status_file"
  fi

  print_report "$report_file"
}

print_report() {
  local report_file="$1"
  while ! mkdir "$LOCK_DIR" 2>/dev/null; do
    sleep 0.05
  done
  cat "$report_file"
  rmdir "$LOCK_DIR"
}

# If argument provided, run only that test
if [[ $# -gt 0 ]]; then
  test_arg="$1"

  # Handle different input formats: base name, filename, or full path
  if [[ "$test_arg" == *.poison ]]; then
    # Remove .poison extension if present
    base_name="${test_arg%.poison}"
  else
    base_name="$test_arg"
  fi

  # Try to find the poison file
  if [[ -f "$EXAMPLES_DIR/$base_name.poison" ]]; then
    poison_file="$EXAMPLES_DIR/$base_name.poison"
  elif [[ -f "$base_name.poison" ]]; then
    poison_file="$base_name.poison"
  elif [[ -f "$test_arg" ]]; then
    poison_file="$test_arg"
  else
    echo "Error: Test file '$test_arg' not found"
    echo "Looking for: $EXAMPLES_DIR/$base_name.poison"
    exit 1
  fi

  poison_files=("$poison_file")
else
  # No argument: run all tests as before
  poison_files=("$EXAMPLES_DIR"/*.poison)
fi

active_jobs=0
for poison_file in "${poison_files[@]}"; do
  run_single_test "$poison_file" &
  ((active_jobs++))
  if (( active_jobs >= JOBS )); then
    wait -n
    ((active_jobs--))
  fi
done

while (( active_jobs > 0 )); do
  wait -n
  ((active_jobs--))
done

for status_file in "$TEMP_DIR"/*.status; do
  [[ -f "$status_file" ]] || continue
  status=$(cat "$status_file")
  base_name=$(basename "$status_file" .status)
  if [[ "$status" == "pass" ]]; then
    ((PASS_COUNT++))
  elif [[ "$status" == "fail" ]]; then
    ((FAIL_COUNT++))
    FAILED_TESTS+=("$base_name")
  fi
done

rm -rf "$TEMP_DIR"

echo -e "\n==== Test Summary ===="
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"
if (( FAIL_COUNT > 0 )); then
  echo "Failed tests:"
  printf ' - %s\n' "${FAILED_TESTS[@]}"
fi
