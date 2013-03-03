#!/bin/sh

TESTNAME=$1
TESTDIR="tests/scanner/input/"
OUTPUTDIR="tests/scanner/output/"
SCANPATH=$TESTDIR$TESTNAME
OUTPATH="$OUTPUTDIR$TESTNAME.out"

echo "File contents: "
cat $SCANPATH

echo "Scanning: $SCANPATH"
./run.sh --target=scan --debug $SCANPATH

echo "\nDiffing vs expected results.. "

diff "$SCANPATH.scan" "$OUTPATH"
rc=$?
if [ $rc -eq 0 ] 
then
    echo "Test succeeded!"
else 
    echo "Test failed.. compare files:"
    echo "Yours: "
    cat "$SCANPATH.scan"
    echo
    echo "Theirs: "
    cat "$OUTPATH"
fi
