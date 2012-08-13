#!/bin/bash


. "$PSI_WORKBENCH_HOME/tools/common.sh"


function usage {
cat <<END
Usage: $COMMANDEXEC [-h] [-n] <file name> [struct name]
    -n   non-interactive mode.
    -h   print this help message and exit.

    If [struct name] is not given, then the default is 'PsiInstance'.
END
}

INTERACTIVE=yes
while getopts 'nh' OPT; do
    case $OPT in
        h) usage; exit ;;
        n) INTERACTIVE=no; shift;;
    esac
done


INSTANCEFILE="$1"
STRUCTNAME="$2"

if [ -z "$INSTANCEFILE" ]; then
    echo -e "Note: the ML instance file expected but not given!\n"
    usage
    exit 1
fi

if [ -z "$STRUCTNAME" ]; then
    STRUCTNAME=PsiInstance
fi


(echo "${STRUCTNAME}.start();"; [ $INTERACTIVE = yes ] && cat
) | "$TOOLSPATH"/sml.sh -i pwb/workbench "@$INSTANCEFILE"

