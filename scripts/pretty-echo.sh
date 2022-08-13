#!/bin/sh

title=${1}
message=${2}

printf "\033[0;32m%12s \e[0m%s\n" "${title}" "${message}"
