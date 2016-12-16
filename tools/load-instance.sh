#!/bin/bash


. "$PSI_WORKBENCH_HOME/tools/common.sh"


function usage {
cat <<END
Usage: $COMMANDEXEC [-h] [-n] [-f] [-c <command file] <file name> [struct name]
    -n   non-interactive mode.
    -h   print this help message and exit.
    -c   read commands from file <command file> instead of opening PWB shell
    -f   turn on profiling

    If [struct name] is not given, then the default is 'PsiInstance'.
END
}

INTERACTIVE=yes
INCOM=
PROFILING=

while getopts 'nhfc:' OPT; do
    case $OPT in
        h) usage; exit ;;
        n) INTERACTIVE=no;;
        f) PROFILING="PolyML.profiling 1;";;
        c) INCOM="$OPTARG";;
    esac
done
shift $(expr $OPTIND - 1 )


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

if [ ! -z "$INCOM" ]; then
    (echo "${PROFILING}${STRUCTNAME}.startFromFile(\"${INCOM}\");"
    ) | "$TOOLSPATH"/sml.sh -i pwb/workbench "@$INSTANCEFILE"    
else
    (echo "${PROFILING}${STRUCTNAME}.start();"; [ $INTERACTIVE = yes ] && cat
    ) | "$TOOLSPATH"/sml.sh -i pwb/workbench "@$INSTANCEFILE"
fi