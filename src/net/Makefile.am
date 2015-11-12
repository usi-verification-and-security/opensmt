SUBDIRS = hiredis

noinst_LTLIBRARIES = libnet.la

AM_CPPFLAGS=$(config_includedirs)

libnet_la_SOURCES = net.C protocol.C
libnet_la_LIBADD = hiredis/libhiredis.la
