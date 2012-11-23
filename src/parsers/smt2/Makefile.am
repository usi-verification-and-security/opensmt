noinst_LTLIBRARIES = libsmt2parser.la

BUILT_SOURCES = smt2parser.cc smt2parser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=smt2
AM_LFLAGS = -olex.yy.c -Psmt2

libsmt2parser_la_SOURCES = smt2parser.yy smt2lexer.ll
