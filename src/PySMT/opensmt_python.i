/* -*- swig -*- */
/* SWIG interface file to create the Python API for OpenSMT  */

%include "typemaps.i"

/***************************************************************************/

/* Convert a python sequence to an array of arguments */

%typemap(in) osmt_expr * {
    int i, sz;
    osmt_expr *tmp;
    void *ptr;
    int r;
    if (!PySequence_Check($input)) {
        PyErr_SetString(PyExc_TypeError, "Sequence object required");
        return NULL;
    }
    sz = PySequence_Size($input);
    tmp = malloc(sizeof(osmt_expr) * sz);
    for (i = 0; i < sz; ++i) {
        PyObject *p = PySequence_ITEM($input, i);
        r = SWIG_ConvertPtr(p, &ptr, SWIGTYPE_p_osmt_expr, 0);
        Py_DECREF(p);
        if (!SWIG_IsOK(r)) {
            free(tmp);
            PyErr_SetString(PyExc_TypeError, "Invalid type for argument, " \
                            "osmt_expr object expected");
            return NULL;
        } else {
            tmp[i] = *((osmt_expr *)(ptr));
        }
     }
    $1 = tmp;
}

/* Free the argument? */
/*
%typemap(freearg) osmt_expr * {
   if ($1) msat_free($1);
}
*/

/* Create the wrappers in python for more pleasant use. */

%pythoncode %{
def mkContext(l):
    return osmt_mk_context(l)

def printTerm(ctx, expr):
    return osmt_print_expr(ctx, expr);

def push(ctx, expr):
    return osmt_push(ctx, expr)

def check(ctx):
    return osmt_check(ctx)

def mkTrue(ctx):
    return osmt_mk_true(ctx)

def mkFalse(ctx):
    return osmt_mk_false(ctx)

def mkBool(ctx, n):
    return osmt_mk_bool_var(ctx, n)

def mkReal(ctx, n):
    return osmt_mk_real_var(ctx, n)

def mkOr(ctx, expr):
    return osmt_mk_or(ctx, expr, len(expr))

def mkAnd(ctx, expr):
    return osmt_mk_and(ctx, expr, len(expr))

def mkEq(ctx, e1, e2):
    return osmt_mk_eq(ctx, e1, e2)

def mkIte(ctx, i, t, e):
    return osmt_mk_ite(ctx, i, t, e)

def mkNot(ctx, e):
    return osmt_mk_not(ctx, e)

def mkImpl(ctx, e1, e2):
    return osmt_mk_impl(ctx, e1, e2)

def mkXor(ctx, e1, e2):
    return osmt_mk_xor(ctx, e1, e2)

def mkNum(ctx, arg):
    if type(arg) is str:
        return osmt_mk_num_from_string(ctx, arg)
    elif type(arg) is int:
        return osmt_mk_num_from_num(ctx, arg)

def mkLeq(ctx, e1, e2):
    return osmt_mk_leq(ctx, e1, e2)
%}


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

/*
%pythoncode %{

## EXTRA_PYTHON_CODE_TAG

%}
*/
