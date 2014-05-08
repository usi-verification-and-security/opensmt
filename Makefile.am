ACLOCAL_AMFLAGS = -I m4
AUTOMAKE_OPTIONS = subdir-objects

SUBDIRS = src

bin_PROGRAMS = opensmt

AM_CPPFLAGS = $(config_includedirs)

opensmt_SOURCES = src/bin/opensmt.C
opensmt_LDFLAGS =
# -lgmpxx -lgmp

LDADD = src/libopensmt.la -lgmpxx -lgmp
