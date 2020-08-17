#!/bin/bash

# remove src/ from the path
path=$1
relPath=`echo ${path#src/}`

cd src && rlwrap idris2 $relPath -p idris2 -p contrib -p network
