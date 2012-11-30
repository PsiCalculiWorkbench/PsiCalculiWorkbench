#!/bin/bash

#
# The script expects PSI_WORKBENCH_HOME to be properly defined
#

. "$PSI_WORKBENCH_HOME/tools/common.sh"
INTERACTIVE=no


function help {
    cat <<END
Usage: $COMMANDEXEC [-h] [-i] uses/path/spec ...

    -h  prints this help message and exits
    -i  lands the SML interpreter into interactive mode
    -o out  compile to the executable file 'out'
END
}


OUT=
while getopts 'iho:' OPT; do
    case $OPT in
        h) help; exit ;;
        i) INTERACTIVE=yes; shift;;
        o) OUT="$OPTARG"; shift;shift;;
    esac
done

#$SML_QUITE_OUTPUT

(
echo -n "use \"$PSI_WORKBENCH_HOME/pwb/bootstrap/bootstrap.ML\";"
for f in "$@"; do echo -ne "uses \"$f\";"; done;
echo
if [ ! -z "$OUT" ]; then
    echo "PolyML.export(\"$OUT\", start);"
fi
[ $INTERACTIVE = yes ] && echo "PwbSml.restoreOutput ();" && cat
) | $SML $SML_OPTS


if [ ! -z "$OUT" ]; then
    echo -n "Compiling: "
    echo $CC $CFLAGS -o "$OUT" "$OUT.o" $LDFLAGS
    $CC $CFLAGS -o "$OUT" "$OUT.o" $LDFLAGS
fi

