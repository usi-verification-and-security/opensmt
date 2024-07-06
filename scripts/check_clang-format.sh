#!/bin/sh

xargs clang-format --Werror --dry-run <.clang-files
