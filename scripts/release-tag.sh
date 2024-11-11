#!/bin/bash

ROOT=$(cd $(dirname "$0")/..; pwd)

## Extract the full version from the top-level CMakeLists.txt
function current_version {
    local str
    for v in MAJOR MINOR PATCH; do
        ## Concatenate particular version parts
        str+=$(sed -n "s/set(OPENSMT_VERSION_${v} \([^ )]*\))/\1/p" <"$ROOT"/CMakeLists.txt).
    done
    str=${str%.}

    printf '%s\n' $str
}

VERSION=$(current_version)
TAG=v${VERSION}
git tag -a $TAG -m "Release $VERSION" || exit $?

printf 'Created release tag "%s"\n' $TAG

read -p 'Do you want to push the tag? [Y/n] ' choice
[[ ${choice,} =~ ^(|y)$ ]] || exit 0

git push origin refs/tags/$TAG
