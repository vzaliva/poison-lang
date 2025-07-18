#!/bin/bash

# Output file
output_file="testResults"

# Empty the output file if it already exists
> "$output_file"

# Iterate over all files in the examples/ directory
for file in examples/*; do
    echo "Running test: $file"

    {
        # Print the test file content
        echo "File: $file"
        cat "$file"

        echo ""
        echo "Result:"
        lake exe poison-interpreter "$file"

        # Separator
        echo "----------------------------"
        echo ""
    } >> "$output_file"

done

echo "All tests completed. Results written to $output_file"
