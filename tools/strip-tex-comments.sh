#!/bin/bash

INFILE=$1
OUTFILE=$2

HOME=`dirname $0`


(cat <<END
PolyML.print_depth(~1);

val dir = OS.FileSys.getDir ();
OS.FileSys.chDir "$HOME";
use "../src/missing.ML";
use "../src/parser.ML";
use "dump-comments.ML";
OS.FileSys.chDir dir;

DC.stripTeXComments "$INFILE" "$OUTFILE"

END
) | poly -q

