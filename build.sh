#!/bin/sh
# build.sh -- Athena build script
# Copyright (C) 2013  Benjamin Barenblat <bbaren@mit.edu>
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the MIT (X11) License as described in the LICENSE file.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.  See the X11 license for more details.

PLATFORM_PACKAGE_DB=/mit/ghc/arch/amd64_deb60/lib/ghc-7.4.2/package.conf.d

add () {
    eval "$( /bin/attach -Padd -b $add_flags "$@" )"
}

cd $(git rev-parse --show-toplevel)
add -f ghc
cabal --package-db=clear --package-db=$PLATFORM_PACKAGE_DB configure
cabal --alex-options="--ghc --template=\"$(git rev-parse --show-toplevel)/alex\""  build
