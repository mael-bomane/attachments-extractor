#!/usr/bin/env bash

set -euo pipefail

INPUT_FILE="${1:-links.txt}"
BASE_DIR="images"

mkdir -p "$BASE_DIR"

group=1
index=1

mkdir -p "$BASE_DIR/$group"

while IFS= read -r line || [[ -n "$line" ]]; do
    # If blank line → new group
    if [[ -z "${line// }" ]]; then
        ((group++))
        index=1
        mkdir -p "$BASE_DIR/$group"
        continue
    fi

    url="$line"

    # remove Discord cropping parameters
    url=$(printf "%s" "$url" | sed -E 's/[?&](width|height)=[0-9]+//g')

    # fix leftover ?&
    url=$(printf "%s" "$url" | sed 's/?&/?/')

    clean=${url%%\?*}
    ext="${clean##*.}"

    filename="$BASE_DIR/$group/$index.$ext"

    curl -L --fail -s "$url" -o "$filename"

    ((index++))

done < "$INPUT_FILE"