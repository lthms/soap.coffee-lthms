#!/usr/bin/bash

function main () {
  local file="${1}"
  local template="${2}"

  tmp_file=$(mktemp)
  generate_json ${file} > ${tmp_file}
  mustache ${tmp_file} ${template} | tail -n +2
  rm ${tmp_file}
}

function gitlog () {
  local file="${1}"
  git --no-pager log \
      --follow \
      --stat=10000 \
      --pretty=format:'%s%n%h%n%H%n%cs%n' \
      "${file}"
}

function parse_filename () {
  local line="${1}"
  local shrink='s/ *\(.*\) \+|.*/\1/'
  local unfold='s/\(.*\){\(.*\) => \(.*\)}/\1\3/'

  echo ${line} | sed -e "${shrink}" | sed -e "${unfold}"
}

function generate_json () {
  local input="${1}"
  local logs="$(gitlog ${input})"

  if [ ! $? -eq 0 ]; then
      exit 1
  fi

  let "idx=0"
  let "last_entry=$(echo "${logs}" | wc -l) / 8"

  local subject=""
  local abbr_hash=""
  local hash=""
  local date=""
  local file=""
  local created="true"
  local modified="false"

  echo -n "{"
  echo -n "\"file\": \"${input}\""
  echo -n ",\"history\": ["

  while read -r subject; do
    read -r abbr_hash
    read -r hash
    read -r date
    read -r # empty line
    read -r file
    read -r # short log
    read -r # empty line

    if [ ${idx} -ne 0 ]; then
      echo -n ","
    fi

    if [ ${idx} -eq ${last_entry} ]; then
      created="true"
      modified="false"
    else
      created="false"
      modified="true"
    fi

    output_json_entry "${subject}" \
                      "${abbr_hash}" \
                      "${hash}" \
                      "${date}" \
                      "$(parse_filename "${file}")" \
                      "${created}" \
                      "${modified}"

    let idx++
  done < <(echo "${logs}")

  echo -n "]}"
}

function output_json_entry () {
  local subject="${1}"
  local abbr_hash="${2}"
  local hash="${3}"
  local date="${4}"
  local file="${5}"
  local created="${6}"
  local last_entry="${7}"

  echo -n "{\"subject\": \"${subject}\""
  echo -n ",\"created\":${created}"
  echo -n ",\"modified\":${modified}"
  echo -n ",\"abbr_hash\":\"${abbr_hash}\""
  echo -n ",\"hash\":\"${hash}\""
  echo -n ",\"date\":\"${date}\""
  echo -n ",\"filename\":\"${file}\""
  echo -n "}"
}

main "$(cat)" "${1}"
