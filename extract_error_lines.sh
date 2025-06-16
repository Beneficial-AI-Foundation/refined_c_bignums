#!/usr/bin/env bash

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
    
    # Calculate the line numbers to display (current line, one before, one after)
    prev_line=$((line_num - 1))
    next_line=$((line_num + 1))
    
    # Print the file name as a header
    echo "$file_path"
    
    # Get and print the lines with their line numbers
    if [[ -f "$file_path" ]]; then
        # Print previous line if it exists
        if [[ $prev_line -gt 0 ]]; then
            printf "%3d: %s\n" $prev_line "$(sed -n "${prev_line}p" "$file_path")"
        fi
        
        # Print the error line
        printf "%3d: %s\n" $line_num "$(sed -n "${line_num}p" "$file_path")"
        
        # Print next line if it exists
        if [[ $(wc -l < "$file_path") -ge $next_line ]]; then
            printf "%3d: %s\n" $next_line "$(sed -n "${next_line}p" "$file_path")"
        fi
    else
        echo "File not found: $file_path"
    fi
    
    echo ""
done
