/* -*- swig -*- */
/* SWIG interface file to create the Python API for OpenSMT  */

%include "typemaps.i"

/***************************************************************************/

/* EXTRA_SWIG_CODE_TAG */

%module opensmt
%{
#include "opensmt_c.h"
/* EXTRA_C_INCLUDE_TAG */
%}


%include "opensmt_c.h"
/* EXTRA_SWIG_INCLUDE_TAG */

%{

/* EXTRA_C_STATIC_CODE_TAG */

%}


%inline %{

/* EXTRA_C_INLINE_CODE_TAG */

%}


%pythoncode %{

## EXTRA_PYTHON_CODE_TAG

%}
