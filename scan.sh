#!/bin/sh
FILENAME=$1

./run.sh --target=scan --debug $1

# Get last argument..
cat "$1.scan"
