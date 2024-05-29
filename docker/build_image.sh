#!/bin/bash

DIR=$(dirname "$0")

REPO=opensmt
TAG=latest
ARGS=()

[[ -n $1 ]] && {
    TARGET=$1
    REPO+=-${TARGET%:*}
    tag=${TARGET#*:}
    [[ -n $tag ]] && TAG=$tag
    ARGS+=(--build-arg "TARGET=$TARGET")
}

exec docker build -t $REPO:$TAG "${ARGS[@]}" "$DIR"
