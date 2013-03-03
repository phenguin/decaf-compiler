#!/bin/sh
# make-tarball.sh -- Athena script to build a tarball for project handin

cd $(git rev-parse --show-toplevel)
add -f ghc
cabal clean
rm -f $USER-handin.tar.gz
tar --transform "s,^\./,$USER-handin/," --exclude '*.tar' --exclude '*.tar.gz' --exclude '*.git/*' --exclude '*~' -czf $USER-handin.tar.gz ./*