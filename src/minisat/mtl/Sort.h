/******************************************************************************************[Sort.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Sort_h
#define Sort_h

#include "Vec.h"

namespace opensmt {

//=================================================================================================
// Some sorting algorithms for vec's


template<class T>
struct LessThan_default {
    bool operator () (T x, T y) { return x < y; }
};


template <class T, class LessThan>
void selectionSort(T* array, int size, LessThan lt)
{
    int     i, j, best_i;
    T       tmp;

    for (i = 0; i < size-1; i++){
        best_i = i;
        for (j = i+1; j < size; j++){
            if (lt(array[j], array[best_i]))
                best_i = j;
        }
        tmp = array[i]; array[i] = array[best_i]; array[best_i] = tmp;
    }
}
template <class T> static inline void selectionSort(T* array, int size) {
    selectionSort(array, size, LessThan_default<T>()); }

template <class T, class LessThan>
void sort(T* array, int size, LessThan lt)
{
    if (size <= 15)
        selectionSort(array, size, lt);

    else{
        T           pivot = array[size / 2];
        T           tmp;
        int         i = -1;
        int         j = size;

        for(;;){
            do i++; while(lt(array[i], pivot));
            do j--; while(lt(pivot, array[j]));

            if (i >= j) break;

            tmp = array[i]; array[i] = array[j]; array[j] = tmp;
        }

        sort(array    , i     , lt);
        sort(&array[i], size-i, lt);
    }
}
template <class T> static inline void sort(T* array, int size) {
    sort(array, size, LessThan_default<T>()); }


template <class T>
void copyArray(T* src, int begin, int end, T* dst) {
    for (int i = begin; i < end; i++)
        dst[i] = src[i];
}

template <class T, class LessThan>
void merge(T* src, int begin, int middle, int end, T* work, LessThan lt)
{
    int i0 = begin;
    int i1 = middle;
    for (int j = begin; j < end; j++) {
        if (i0 < middle && (i1 >= end || lt(src[i0], src[i1])))
            work[j] = src[i0++];
        else
            work[j] = src[i1++];
    }
}

template <class T, class LessThan>
void splitMerge(T* src, int begin, int end, T* work, LessThan lt)
{
    if (end-begin <= 1) return;
    int middle = (end+begin)/2;
    splitMerge(src, begin, middle, work, lt);
    splitMerge(src, middle, end, work, lt);
    merge(src, begin, middle, end, work, lt);
    copyArray(work, begin, end, src);
}

template <class T, class LessThan> static inline
void mergeSort(T* src, int size, LessThan lt) {
    T* work = (T*)malloc(sizeof(T)*size);
    splitMerge(src, 0, size, work, lt);
    free(work);
}

//=================================================================================================
// For 'vec's:


template <class T, class LessThan> void sort(vec<T>& v, LessThan lt) {
    sort((T*)v, v.size(), lt); }
template <class T> void sort(vec<T>& v) {
    sort(v, LessThan_default<T>()); }

template<class T> void uniq(vec<T>& v) {
        int j, i;
        if (v.size() == 0) return;
        T* prev = &v[0];
        for (i = 1, j = 1; i < v.size(); i++) {
            if (v[i] != *prev) {
                v[j++] = v[i];
                prev = &v[i];
            }
        }
        v.shrink(i-j);
}

//=================================================================================================

}

#endif
