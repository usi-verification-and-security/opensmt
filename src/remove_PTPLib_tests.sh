#!/usr/bin/env sh
# -*- coding: utf-8 -*-

cd "$(dirname "$1")"
if [ -d ptplib-src/tests ]; then rm -rf ptplib-src/tests; fi
if [ -d ptplib-src/.circleci ]; then rm -rf ptplib-src/.circleci; fi
if [ -d ptplib-src/ci ]; then rm -rf ptplib-src/ci; fi