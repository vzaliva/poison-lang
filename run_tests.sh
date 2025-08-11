#!/bin/bash


EXAMPLES_DIR="examples"
PASS_COUNT=0
FAIL_COUNT=0
FAILED_TESTS=()

TEMP_DIR="testResults"
mkdir -p "$TEMP_DIR"


for poison_file in "$EXAMPLES_DIR"/*.poison; do
    base_name=$(basename "$poison_file" .poison)
    result_file="$TEMP_DIR/$base_name.result"
    if [[ -f "$EXAMPLES_DIR/$base_name.output" ]]; then
        expected_output="$EXAMPLES_DIR/$base_name.output"
    else
        expected_output="$EXAMPLES_DIR/$base_name.fail"
    fi

   
    lake exe poison-interpreter "$poison_file" > "$result_file" 2>&1 || true
    
    # Compare result with expected output 
    if diff -q "$result_file" "$expected_output" > /dev/null; then
        echo "Passed: $base_name"
        ((PASS_COUNT++))
    else
        echo 
        echo "Failed: $base_name"
        echo "**************************"
        echo "Expected Output:"
        cat "$expected_output"
        echo 
        echo "--------------------------"
        echo "Actual Output:"
        cat "$result_file"
        echo
        echo "**************************"
        FAILED_TESTS+=("$base_name")
        ((FAIL_COUNT++))
    fi
done

# Cleanup
rm -rf "$TEMP_DIR"

# Summary
echo ""
echo "==== Test Summary ===="
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"
if [ $FAIL_COUNT -ne 0 ]; then
    echo "Failed tests:"
    for test in "${FAILED_TESTS[@]}"; do
        echo " - $test"
    done
fi

