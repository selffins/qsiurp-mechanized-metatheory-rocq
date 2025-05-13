#!/bin/bash

ORG_DIR="."
OUTPUT_DIR="."

lisp_setup="
(progn (require 'ox-html)
       (org-html-export-to-html))
"
# Find and convert all .org files
for file in "$ORG_DIR"/*.org; do
    if [ -f "$file" ]; then
        base_name=$(basename "$file" .org)
        emacs --batch "$file" --eval="${lisp_setup}"
        mv "${base_name}.html" "$OUTPUT_DIR/"
        echo "Converted: $file → $OUTPUT_DIR/${base_name}.html"
    fi
done
