#!/usr/bin/env bash

# Script to run all .poison files in the examples directory and save output
# based on exit code: 0 -> .output, non-zero -> .fail

set -euo pipefail

# Change to the poison-lang directory
cd "$(dirname "$0")"

# Check if lake and poison-interpreter are available
if ! command -v lake &> /dev/null; then
    echo "Error: lake command not found"
    exit 1
fi

if command -v nproc >/dev/null 2>&1; then
    JOBS=$(nproc)
elif command -v sysctl >/dev/null 2>&1; then
    JOBS=$(sysctl -n hw.ncpu 2>/dev/null || echo 1)
else
    JOBS=1
fi

print_usage() {
    echo "Usage: $0 [-j|--jobs N]"
    echo "  -j, --jobs N   Number of parallel executions (default: CPU count)"
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
        -*)
            echo "Error: Unknown option '$1'"
            print_usage
            exit 1
            ;;
        *)
            echo "Error: Unexpected argument '$1'"
            print_usage
            exit 1
            ;;
    esac
done

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
    echo "Error: --jobs must be a positive integer"
    exit 1
fi

process_single_file() {
    local poison_file="$1"
    local base_name
    local temp_output
    local directive_line
    local directive
    local -a extra_args
    local -a directive_args

    base_name=$(basename "$poison_file" .poison)
    echo "Processing: $poison_file"

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

    temp_output=$(mktemp)
    if lake exe poison-interpreter --verbose "${extra_args[@]}" "$poison_file" > "$temp_output" 2>&1; then
        rm -f "examples/${base_name}.fail"
        mv "$temp_output" "examples/${base_name}.output"
        echo "  ✓ Success: saved to examples/${base_name}.output"
    else
        rm -f "examples/${base_name}.output"
        mv "$temp_output" "examples/${base_name}.fail"
        echo "  ✗ Failed: saved to examples/${base_name}.fail"
    fi
}

active_jobs=0
for poison_file in examples/*.poison; do
    process_single_file "$poison_file" &
    active_jobs=$((active_jobs + 1))
    if (( active_jobs >= JOBS )); then
        wait -n
        active_jobs=$((active_jobs - 1))
    fi
done

while (( active_jobs > 0 )); do
    wait -n
    active_jobs=$((active_jobs - 1))
done

echo "All tests updated!"
