#!/bin/bash

BEGIN_MARKER="# begin generated files"
END_MARKER="# begin generated files"

sed -i -e "/${BEGIN_MARKER}/,/${END_MARKER}/d" .gitignore
sed -i -e :a -e '/^\n*$/{$d;N;};/\n$/ba' .gitignore

echo "" >> .gitignore
echo ${BEGIN_MARKER} >> .gitignore
for f in $@; do
    echo "${f}" >> .gitignore
done
echo ${END_MARKER} >> .gitignore
