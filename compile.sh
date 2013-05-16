#!/bin/sh
FILENAME=$1

./run.sh --target=assembly --debug "$1.dcf" -o "$1.s"
gcc -g "$1.s" -o $1 ; "./$1"

