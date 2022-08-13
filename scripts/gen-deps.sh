#!/bin/sh

input=${1}
output=${2}

proc="$(basename ${input} | cut -f 1 -d '.')"

echo "include ${input}" > ${output}
echo "prebuild : ${proc}-prebuild" >> ${output}
echo "build : ${proc}-build" >> ${output}
echo "postbuild : ${proc}-postbuild" >> ${output}
echo "${proc}-build : ${proc}-prebuild" >> ${output}
echo "${proc}-postbuild : ${proc}-build" >> ${output}
echo ".PHONY : ${proc}-prebuild ${proc}-build ${proc}-postbuild" >> ${output}
