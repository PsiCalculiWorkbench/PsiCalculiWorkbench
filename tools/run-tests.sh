#!/bin/bash

SML="$TOOLSPATH/pwb sml -i"
TESTDIR="$PSI_WORKBENCH_HOME/tests"

function help {
    cat <<END
Usage: $COMMANDEXEC [-h] [test name prefix]

    -h  prints this help message and exits

    If 'test name prefix' is given, then this command only runs those tests
    which file names begin with the prefix. Otherwise runs all tests in the
    tests/ directory.
END
}

[ "$1" = "-h" ] && help && exit


PREFIX="$1"

echo "PwbLog.pushLoggerStdErr PwbTestRunner.loggerName; PwbTestRunner.runPrefixInDir \"$PREFIX\" \"$TESTDIR\";" | $SML 'pwb/pwb-test'

