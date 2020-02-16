#!/usr/bin/bash

function commits_count () {
    local file=${1}
    local res=$(git --no-pager log --pretty=format:"" "${file}" | wc -l)

    if [ ! $? -eq 0 ]; then
        exit 1
    fi

    echo -n "$(( ${res} ))"
}

function print_commit_format () {
    local file=${1}
    local nth=${2}
    local format=${3}

    git --no-pager log --skip=${nth} -n1 --pretty=format:"${format}" "${file}"
}

function generate_json_history () {
  local file="${1}"
  local count=$(commits_count ${file})

  echo "{"
  echo "  \"file\" : \"${file}\","
  echo "  \"history\" :"
  echo "    ["
  for i in $(seq 0 ${count}); do
      subject="$(print_commit_format ${file} ${i} '%s')"
      abbr_hash="$(print_commit_format ${file} ${i} '%h')"
      hash="$(print_commit_format ${file} ${i} '%H')"
      date="$(print_commit_format ${file} ${i} '%cs')"

  echo "      {"
  echo "        \"subject\" : \"${subject}\","
  echo "        \"abbr_hash\" : \"${abbr_hash}\","
  echo "        \"hash\" : \"${hash}\","
  echo "        \"date\" : \"${date}\""
  echo -n \
       "      }"

      if [ ! ${i} -eq ${count} ]; then
          echo ","
      else
          echo ""
      fi
  done

  echo "    ]"
  echo "}"
}

FILE=`cat`

tmp_file=$(mktemp)
generate_json_history ${FILE} > ${tmp_file}
haskell-mustache ${1} ${tmp_file}
rm ${tmp_file}
