#!/usr/bin/env bash

# Function to extract line content from a file
get_line_content() {
    local file=$1
    local line_num=$2
    
    if [[ -f "$file" ]]; then
        sed -n "${line_num}p" "$file"
    else
        echo "File not found: $file"
    fi
}

# Process input from stdin or a file provided as argument
input_source="/dev/stdin"
if [[ $# -gt 0 && -f "$1" ]]; then
    input_source="$1"
fi

# Use grep to find error lines, then process each match
grep -o "File \"[^\"]*\", line [0-9]*, characters [0-9]*-[0-9]*:" "$input_source" | while read -r error_line; do
    # Extract file path and line number
    file_path=$(echo "$error_line" | sed -E 's/File "(.+)", line ([0-9]+).*/\1/')
    line_num=$(echo "$error_line" | sed -E 's/File ".+", line ([0-9]+).*/\1/')
    
    # Remove leading "./" from file path if present
    file_path=${file_path#./}
    
    # Get the content of the specified line
    line_content=$(get_line_content "$file_path" "$line_num")
    
    # Print the result
    echo "Line $line_num of $file_path is"
    echo "$line_content"
    echo ""
done
