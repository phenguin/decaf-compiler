#!/bin/sh
FILENAME=$1

./run.sh --target=assembly "$1.dcf" > "$1.s"
gcc "$1.s" -o $1 ; "./$1"

