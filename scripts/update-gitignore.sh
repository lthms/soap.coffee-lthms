#!/bin/bash

BEGIN_MARKER="# begin generated files"
END_MARKER="# begin generated files"

# remove the previous list of generated files to ignore
sed -i -e "/${BEGIN_MARKER}/,/${END_MARKER}/d" .gitignore
# remove trailing empty lines
sed -i -e :a -e '/^\n*$/{$d;N;};/\n$/ba' .gitignore

# output the list of files to ignore
echo "" >> .gitignore
echo ${BEGIN_MARKER} >> .gitignore
for f in $@; do
    echo "${f}" >> .gitignore
done
echo ${END_MARKER} >> .gitignore
