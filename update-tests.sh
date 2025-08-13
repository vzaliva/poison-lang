#!/usr/bin/env bash

# Script to run all .poison files in the examples directory and save output
# based on exit code: 0 -> .output, non-zero -> .fail

set -e  # Exit on any error

# Change to the poison-lang directory
cd "$(dirname "$0")"

# Check if lake and poison-interpreter are available
if ! command -v lake &> /dev/null; then
    echo "Error: lake command not found"
    exit 1
fi

# Iterate over all .poison files in the examples directory
for poison_file in examples/*.poison; do
    # Extract the base filename without extension
    base_name=$(basename "$poison_file" .poison)
    
    echo "Processing: $poison_file"
    
    # Run the poison interpreter and capture both stdout and stderr
    # Use a temporary file to capture output
    temp_output=$(mktemp)
    
    if lake exe poison-interpreter "$poison_file" > "$temp_output" 2>&1; then
        # Exit code was 0, save to .output file
        mv "$temp_output" "examples/${base_name}.output"
        echo "  ✓ Success: saved to examples/${base_name}.output"
    else
        # Exit code was non-zero, save to .fail file
        mv "$temp_output" "examples/${base_name}.fail"
        echo "  ✗ Failed: saved to examples/${base_name}.fail"
    fi
done

echo "All tests updated!"

