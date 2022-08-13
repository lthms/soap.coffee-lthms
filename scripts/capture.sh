#!/bin/sh

logfile=logs/$(echo ${1} | sed -e 's/\//--/g')

shift 1

"$@" 1> ${logfile}.stdout 2> ${logfile}.stderr
exitcode=$?

if [[ ! ${exitcode} -eq 0 ]]; then
    echo "An error occurred, see ${logfile}.stdout and ${logfile}.stderr"
    exit ${exitcode}
fi
