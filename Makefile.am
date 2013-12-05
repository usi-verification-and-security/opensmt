ACLOCAL_AMFLAGS = -I m4

SUBDIRS = src

bin_PROGRAMS = opensmt

INCLUDES = $(config_includedirs)

opensmt_SOURCES = src/bin/opensmt.C
opensmt_LDFLAGS =
# -lgmpxx -lgmp

LDADD = src/libopensmt.la -lgmpxx -lgmp
