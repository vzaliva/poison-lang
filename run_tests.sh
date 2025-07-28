#!/bin/bash

# Output file
output_file="testResults"


> "$output_file"


for file in examples/*; do
    echo "Running test: $file"

    {
        # Print the test file content
        echo "File: $file"
        cat "$file"

        echo ""
        echo "Result:"
        lake exe poison-interpreter "$file"

       
        echo "----------------------------"
        echo ""
    } >> "$output_file"

done

echo "All tests completed. Results written to $output_file"
