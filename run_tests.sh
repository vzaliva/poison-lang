#!/usr/bin/env bash
set -u

EXAMPLES_DIR="examples"
INTERP_FLAGS=""

# Optional flag: --big to use big-step semantics
if [[ ${1-} == "--big" ]]; then
  INTERP_FLAGS="--big"
  shift
fi
TEMP_DIR="testResults"
mkdir -p "$TEMP_DIR"

PASS_COUNT=0
FAIL_COUNT=0
FAILED_TESTS=()

for poison_file in "$EXAMPLES_DIR"/*.poison; do
  base_name=$(basename "$poison_file" .poison)
  result_file="$TEMP_DIR/$base_name.result"

  if [[ -f "$EXAMPLES_DIR/$base_name.output" ]]; then
    expected="$EXAMPLES_DIR/$base_name.output"
    expect_type="output"
  elif [[ -f "$EXAMPLES_DIR/$base_name.fail" ]]; then
    expected="$EXAMPLES_DIR/$base_name.fail"
    expect_type="fail"
  else
    echo "Skipping $base_name: no .output or .fail"
    continue
  fi

  # Run interpreter and capture exit code (stdout+stderr -> result_file)
  lake exe poison-interpreter $INTERP_FLAGS "$poison_file" > "$result_file" 2>&1
  exit_code=$?

  # Check whether output matches expected
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
    echo "Passed: $base_name"
    ((PASS_COUNT++))
  else
    echo -e "\nFailed: $base_name"
    echo "**************************"
    echo "Expected ($expected):"
    cat "$expected"
    echo -e "\n--------------------------\nActual ($result_file):"
    cat "$result_file"
    echo -e "\nDiff:"
    diff -u "$expected" "$result_file" || true
    echo "**************************"
    FAILED_TESTS+=("$base_name")
    ((FAIL_COUNT++))
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
