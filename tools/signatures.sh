#!/bin/bash

function usage {
    echo "$COMMANDEXEC [-h] [-d] [-o out-file.pdf] <ml files ...>"
    echo "    -d - instead of outputting a PDF file, dumps a GraphViz dot file"
}

DUMPDOT=0
OUT=-

while getopts 'o:hd' OPT; do
    case $OPT in
        h) usage; exit ;;
        o) OUT="$OPTARG"; shift;shift;;
        d) DUMPDOT=1; shift;;
    esac
done

[ "$OUT" = '-' ] && DOTOPTS= || DOTOPTS=-o"$OUT"

cat "$@" | "$TOOLSPATH"/signatures.pl | (
    if [ "$DUMPDOT" = 1 ]; then
        if [ "$OUT" = '-' ]; then
            cat
        else
            cat > "$OUT"
        fi
    else
        dot -Tpdf $DOTOPTS
    fi
)


