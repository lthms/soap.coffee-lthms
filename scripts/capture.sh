#!/bin/sh

logfile=logs/$(echo ${1} | sed -e 's/\//--/g')

shift 1

"$@" 1> ${logfile}.stdout 2> ${logfile}.stderr
exitcode=$?

if [[ ! ${exitcode} -eq 0 ]]; then
    echo -e "\033[0;31mError:\033[0m '"$@"' returned ${exitcode}"
    echo -e "See \033[0;33m${logfile}.stdout\033[0m and \033[0;33m${logfile}.stderr\033[0m"
    exit ${exitcode}
fi
