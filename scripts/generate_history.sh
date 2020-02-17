#!/usr/bin/bash

FORMAT="{\"subject\":\"%s\",\"abbr_hash\":\"%h\",\"hash\":\"%H\",\"date\":\"%cs\""

function generate_history_json () {
    local file="${1}"

    local logs=$(git --no-pager log --follow --pretty=format:"${FORMAT}" "${file}")

    if [ ! $? -eq 0 ]; then
        exit 1
    fi

    local count=0
    local name="${file}"

    while read -r line; do
        local hash=$(echo "${line}}" | jq -j '.hash')

        local pre_name="$(git --no-pager show --stat=10000 ${hash} | sed -e 's/ *\(.*\){\(.*\) => \(.*\)}/\1\2 => \1\3/'  | grep "=> ${name}" | xargs | cut -d' ' -f1)"

        if [[ ! -z "${pre_name}" ]]; then
            name="$(echo ${pre_name})"
        fi

        if [[ ${count} -eq 0 ]]; then
            echo -n "[ "
        else
            echo -n ", "
        fi

        echo "${line}, \"filename\":\"${name}\"}"

        count=$(( ${count} + 1 ))
    done < <(echo "${logs}")

    echo -n "]"
}

function generate_json () {
  local file="${1}"

  echo "{"
  echo "  \"file\" : \"${file}\","
  echo "  \"history\" : $(generate_history_json "${file}")"
  echo "}"
}

FILE=`cat`

tmp_file=$(mktemp)
generate_json ${FILE} > ${tmp_file}
haskell-mustache ${1} ${tmp_file}
rm ${tmp_file}
