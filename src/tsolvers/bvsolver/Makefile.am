SUBDIRS = minisatp

noinst_LTLIBRARIES = libbvsolver.la

AM_CPPFLAGS=$(config_includedirs)

libbvsolver_la_SOURCES = BVSolver.h BVSolver.C BitBlaster.h BitBlaster.C
libbvsolver_la_LIBADD = minisatp/libminisatp.la
