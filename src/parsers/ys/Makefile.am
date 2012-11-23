noinst_LTLIBRARIES = libysparser.la

BUILT_SOURCES = ysparser.cc ysparser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=ys
AM_LFLAGS = -olex.yy.c -Pys

libysparser_la_SOURCES = ysparser.yy yslexer.ll
