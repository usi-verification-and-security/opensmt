AC_PREREQ(2.59)
AC_INIT([OpenSMT 2.0], [(unstable)], [antti.hyvarinen@gmail.com])
AC_CONFIG_AUX_DIR(autotools)
AM_INIT_AUTOMAKE
AC_CONFIG_MACRO_DIR([m4])

AC_PROG_CC
AC_PROG_CXX
AC_PROG_YACC
AM_PROG_LEX
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_MAKE_SET

LT_INIT
AC_DISABLE_SHARED

AC_ARG_ENABLE(library,
  AC_HELP_STRING([--enable-library],
                 [produces OpenSMT libraries (default=no)]),
  want_library="yes",
  want_library="no")

AM_CONDITIONAL([WANT_LIBRARY], [test "$want_library" = "yes"])

#
# Statically linked version
#
AC_ARG_ENABLE(statically,
  AC_HELP_STRING([--enable-statically],
                 [enable statically linked libraries (-static) (default=no)]),
  enablestatically=$enableval,
  enablestatically="no")

if test $enablestatically = "yes" ;
then
  config_statically="-static"
elif test $enablestatically = "no" ;
then
  config_statically="" 
else
  config_statically=$enablestatically
fi
echo "setting static flags to... ${config_statically:-none}"
# 
# Profiling
#
AC_ARG_ENABLE(profiling,
  AC_HELP_STRING([--enable-profiling],
                 [enable profiling (-pg) (default=no)]),
  enableprofiling=$enableval,
  enableprofiling="no")

if test $enableprofiling = "yes" ;
then
  config_profiling="-pg"
elif test $enableprofiling = "no" ;
then
  config_profiling=""
else
  config_profiling=$enableprofiling
fi
echo "setting profiling flags to... ${config_profiling:-none}"
#
# Optimization
#
AC_ARG_ENABLE(optimization,
  AC_HELP_STRING([--enable-optimization],
                 [enable optimization by compiler (-O3) (default=yes)]),
  enableoptimization=$enableval,
  enableoptimization="yes")

if test $enableoptimization = "yes" ;
then
  config_optimization="-O3 -DOPTIMIZE -DNDEBUG"
elif test $enableoptimization = "no" ;
then
  config_optimization="-O0"
else
  config_optimization=$enableoptimization
fi
echo "setting optimization flags to... ${config_optimization:-none}"
#
# Proof production
#
AC_ARG_ENABLE(proof,
  AC_HELP_STRING([--enable-proof],
                 [enable proof production (default=no)]),
  enableproof=$enableval,
  enableproof="no")

if test $enableproof = "yes" ;
then
  config_proof="-DPRODUCE_PROOF"
elif test $enableproof = "no" ;
then
  config_proof=""
else
  config_proof=$enableproof
fi
echo "setting proof flags to... ${config_proof:-none}"
#
# Enable Pedantic Assertion Checking
#
AC_ARG_ENABLE(pedantic_debug,
  AC_HELP_STRING([--enable-pedantic_debug],
                 [enable pedantic assertion checking (default=no)]),
  enablepedantic_debug=$enableval,
  enablepedantic_debug="no")

if test $enablepedantic_debug = "yes" ;
then
  config_pedantic_debug="-DPEDANTIC_DEBUG"
elif test $enablepedantic_debug = "no" ;
then
  config_pedantic_debug=""
else
  config_pedantic_debug=$enablepedantic_debug
fi
echo "setting pedantic debug flags to... ${config_pedantic_debug:-none}"
#
# Enable GC debug
#
AC_ARG_ENABLE(gcdebug,
  AC_HELP_STRING([--enable-gcdebug],
                 [enable garbage collection debug (default=no)]),
  enablegc_debug=$enableval,
  enablegc_debug="no")

if test $enablegc_debug = "yes" ;
then
  config_gc_debug="-DGC_DEBUG"
elif test $enablegc_debug = "no" ;
then
  config_gc_debug=""
else
  config_gc_debug=$enablegc_debug
fi
echo "setting garbage collection debug flags to... ${config_gc_debug:-none}"
#
# SMTCOMP version
#
AC_ARG_ENABLE(smtcomp,
  AC_HELP_STRING([--enable-smtcomp],
                 [enable smtcomp mode (default=no)]),
  enablesmtcomp=$enableval,
  enablesmtcomp="no")

if test $enablesmtcomp = "yes" ;
then
  config_smtcomp="-DSMTCOMP -march=opteron -static"
elif test $enablesmtcomp = "no" ;
then
  config_smtcomp=""
else
  config_smtcomp=$enablesmtcomp
fi
echo "setting smtcomp flags to... ${config_smtcomp:-none}"

# Complain if both pedantic debug and optimization are enabled
if test $enablepedantic_debug = "yes" -a $enableoptimization = "yes" ;
then
  echo "Error: cannot enable both pedantic debug and optimization"
  exit
fi

# Complain if smtcomp is enabled and optimization is disabled
if test $enablesmtcomp = "yes" -a $enableoptimization = "no" ;
then
  echo "Error: smtcomp requires optimizations"
  exit
fi

# Complain if smtcomp is enabled and proof is enabled
if test $enablesmtcomp = "yes" -a $enableproof = "yes" ;
then
  echo "Error: cannot enable proof with smtcomp"
  exit
fi

AM_CFLAGS="-W -Wall -g -Wno-deprecated $config_profiling $config_optimization $config_pedantic_debug $config_gc_debug $config_smtcomp $config_statically $config_proof"
AM_CXXFLAGS="-W -Wall -g -Wno-deprecated $config_profiling $config_optimization $config_pedantic_debug $config_gc_debug $config_smtcomp $config_statically $config_proof"
CFLAGS=""
CXXFLAGS=""

# Allow user to use a GMP lib in a non-standard location
AC_ARG_WITH([gmp],
	    [AS_HELP_STRING([--with-gmp=prefix],
			    [Use this when GMP is in a non-standard location (e.g /opt/local in MacPorts)])],
			    [NONSTDGMPPATH=1],
			    [NONSTDGMPPATH=0])
if test $NONSTDGMPPATH = 1 ; then
  AM_CXXFLAGS="$AM_CXXFLAGS -I$with_gmp/include"
  AM_LDFLAGS="$AM_LDFLAGS -L$with_gmp/lib"
fi

AC_SUBST(AM_CFLAGS)
AC_SUBST(AM_CXXFLAGS)
AC_SUBST(CFLAGS)
AC_SUBST(CXXFLAGS)
AC_SUBST(AM_LDFLAGS)

# Setup comilation/linking flags for library checks
OLDCPPFLAGS=$CPPFLAGS
CPPFLAGS=$CXXFLAGS
OLDLDFLAGS=$LDFLAGS
LDFLAGS="$LDFLAGS $AM_LDFLAGS"

# Check for GMP header
GMP_HEADER_FOUND=1
if test $NONSTDGMPPATH = 1 ; then
	AC_CHECK_HEADERS($with_gmp/include/gmp.h,
			 ,
			 [AC_MSG_ERROR([ The GMP header gmp.h was not found.])])

else
	AC_CHECK_HEADERS(gmp.h,
			 ,
			 [AC_MSG_ERROR([ The GMP header gmp.h was not found.])])
fi
# Check for GMP library
AC_CHECK_LIB(gmp, __gmpz_init, ,[AC_MSG_ERROR([GMP library not found])])

# Check for readline library
AC_ARG_WITH([readline],
            [AS_HELP_STRING([--with-readline],
              [support fancy command line editing @<:@default=check@:>@])],
            [],
            [with_readline=check])

LIBREADLINE=
AS_IF([test "x$with_readline" != xno],
      [AC_CHECK_LIB([readline], [main],
                    [AC_SUBST([LIBREADLINE], ["-lreadline -lncurses"])
                     AC_DEFINE([HAVE_LIBREADLINE], [1],
                               [Define if you have libreadline])
                    ],
                    [if test "x$with_readline" != xcheck; then
                        AC_MSG_FAILURE([--with-readline was given, but test for readline failed])
                     fi
                    ], -lncurses)])


# Restore original flags
CPPFLAGS=$OLDCPPFLAGS
LDFLAGS=$OLDLDFLAGS

#
# List of directories to include
#
config_includedirs="-I\${top_srcdir}/src \\
-I\${top_srcdir}/src/minisat/mtl \\
-I\${top_srcdir}/src/minisat/core \\
-I\${top_srcdir}/src/simplifiers \\
-I\${top_srcdir}/src/common \\
-I\${top_srcdir}/src/egraph \\
-I\${top_srcdir}/src/sorts \\
-I\${top_srcdir}/src/symbols \\
-I\${top_srcdir}/src/pterms \\
-I\${top_srcdir}/src/logics \\
-I\${top_srcdir}/src/smtsolvers \\
-I\${top_srcdir}/src/cnfizers \\
-I\${top_srcdir}/src/proof \\
-I\${top_srcdir}/src/api \\
-I\${top_srcdir}/src/tsolvers \\
-I\${top_srcdir}/src/tsolvers/emptysolver \\
-I\${top_srcdir}/src/tsolvers/bvsolver \\
-I\${top_srcdir}/src/tsolvers/bvsolver/minisatp \\
-I\${top_srcdir}/src/tsolvers/lrasolver \\
-I\${top_srcdir}/src/tsolvers/liasolver \\
-I\${top_srcdir}/src/tsolvers/ctsolver \\
-I\${top_srcdir}/src/tsolvers/axdiffsolver \\
-I\${top_srcdir}/src/tsolvers/dlsolver \\
-I\${top_srcdir}/src/attributes"

AC_SUBST(config_includedirs)

AC_CONFIG_FILES([ \
		  Makefile \
		  src/Makefile \
		  src/parsers/Makefile \
		  src/parsers/smt2new/Makefile \
		  src/cnfizers/Makefile \
		  src/simplifiers/Makefile \
		  src/smtsolvers/Makefile \
		  src/proof/Makefile \
		  src/common/Makefile \
		  src/egraph/Makefile \
		  src/sorts/Makefile \
		  src/logics/Makefile \
		  src/symbols/Makefile \
		  src/pterms/Makefile \
		  src/tsolvers/Makefile \
		  src/tsolvers/emptysolver/Makefile \
		  src/tsolvers/axdiffsolver/Makefile \
		  src/tsolvers/bvsolver/Makefile \
		  src/tsolvers/bvsolver/minisatp/Makefile \
		  src/tsolvers/lrasolver/Makefile \
		  src/tsolvers/ctsolver/Makefile \
		  src/tsolvers/dlsolver/Makefile \
		  src/api/Makefile \
		  test/Makefile \
		  ])

AC_OUTPUT
