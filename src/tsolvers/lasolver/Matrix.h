//
// Created by prova on 24.08.18.
//

#ifndef OPENSMT_MATRIX_H
#define OPENSMT_MATRIX_H

#include <Real.h>
#include <Vec.h>
#include <Alloc.h>
#include "ArithLogic.h"
//
// Class to store the term of constraints as a column of Simplex method tableau
//
class LAVec
{
    friend class LAVecAllocator;

private:
    struct {
        bool     reloced : 1;
        unsigned size    : 31; // Vector size
    } header;

    opensmt::Real den;
    opensmt::Real args[0]; // Either the elements or the relocation reference

public:
    LAVec(std::vector<opensmt::Real>&& ps, const opensmt::Real& den) : den(den) {
        header.size = ps.size();
        header.reloced = 0;
        for (size_t i = 0; i < ps.size(); i++) {
            new (&args[i]) opensmt::Real(ps[i]);
        }
    }
    int size() const { return header.size; }
    opensmt::Real& operator[] (int i) { assert(i >= 1); assert(i <= size()); return args[i-1]; }
    const opensmt::Real& operator[] (int i) const { assert( i >= 1 && i <= size()); return args[i-1]; }

    void operator= (const LAVec& o) {
        for (int i = 0; i < size(); i++)
            args[i] = o.args[i];
    }
};

struct LAVecRef{
    uint32_t x;
    inline friend bool operator== (const LAVecRef& a1, const LAVecRef& a2)   { return a1.x == a2.x; }
    inline friend bool operator!= (const LAVecRef& a1, const LAVecRef& a2)   { return a1.x != a2.x; }
    inline friend bool operator< (const LAVecRef& a1, const LAVecRef& a2)    { return a1.x > a2.x;  }
};

static struct LAVecRef LAVecRef_Undef = {INT32_MAX};

class LAVecAllocator : public RegionAllocator<uint32_t>
{
    unsigned n_vecs;
    static int lavecWord32Size(int sz) {
        return (sizeof(LAVec) + (sizeof(opensmt::Real) * sz)) / sizeof(uint32_t); }
private:
    vec<LAVecRef>   lavecs;
public:
    inline void   clear() override { lavecs.clear(); RegionAllocator::clear(); }
    LAVecAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), n_vecs(0) {}
    LAVecAllocator()                   : n_vecs(0) {}
    unsigned getNumVecs() const { return n_vecs; };

    LAVecRef alloc(std::vector<opensmt::Real>&& ps, const opensmt::Real& den) {
        uint32_t v = RegionAllocator<uint32_t>::alloc(lavecWord32Size(ps.size()));
        LAVecRef vid = {v};
        new (lea(vid)) LAVec(std::move(ps), den);
        n_vecs++;
        return vid;
    }

    LAVec&       operator[](LAVecRef r)       { return (LAVec&)RegionAllocator<uint32_t>::operator[](r.x); }
    const LAVec& operator[](LAVecRef r) const { return (LAVec&)RegionAllocator<uint32_t>::operator[](r.x); }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    LAVec*       lea       (LAVecRef r)       { return (LAVec*)RegionAllocator<uint32_t>::lea(r.x); }
    const LAVec* lea       (LAVecRef r) const { return (LAVec*)RegionAllocator<uint32_t>::lea(r.x); }
    LAVecRef     ael       (const LAVec* t)   { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LAVecRef rf; rf.x = r; return rf; }
    void         free      (LAVecRef)         {}
    // Debug stuff
    char*        printVec (LAVecRef r)  const;
};

class LAVecStore
{
private:
    vec<LAVecRef>   lavecs;
    LAVecAllocator& lva;
    ArithLogic&     logic;
public:
    LAVecStore(LAVecAllocator& lva, ArithLogic & logic) : lva(lva), logic(logic) {}
    inline void   clear() { lavecs.clear(); };
    LAVecRef getNewVec(std::vector<opensmt::Real>&& ps, const opensmt::Real& den);
    LAVecRef getNewVec(std::vector<opensmt::Real>&& ps) { return getNewVec(std::move(ps), 1); }
    LAVecRef getNewVec(int size) { std::vector<opensmt::Real> tmp; tmp.resize(size); return getNewVec(std::move(tmp)); }
    int    numVecs() const ;
    void   remove(const LAVecRef r);
    LAVec& operator [] (LAVecRef vr) { return lva[vr]; }
    char* print(LAVecRef vr);
};

class LAMatrix
{
private:
    LAVecRef coeffs;
    int cols;
    int rows;
public:
    LAMatrix() : coeffs(LAVecRef_Undef), cols(0), rows(0) {}
    LAMatrix(LAVecRef coeffs, int rows, int cols) : coeffs(coeffs), cols(cols), rows(rows) {}
    int nRows() const { return rows; }
    int nCols() const { return cols; }
    LAVecRef getCoeffs() const { return coeffs; }
};

struct MId {
    uint32_t x;
    bool operator== (const MId& o) { return x == o.x; }
    bool operator!= (const MId& o) { return x != o.x; }
};

const MId MId_Undef { UINT32_MAX };

class LAMatrixStore
{
private:
    LAVecStore& vs;
    vec<LAMatrix> matrices;
public:
    // Access the element of matrix id at column col, row row.
    opensmt::Real& MM(MId id, int row, int col);
    LAMatrixStore(LAVecStore& vs) : vs(vs) {}
    void clear() { matrices.clear(); }
    // Return an n x m matrix full of 0s
    MId getNewMatrix(int rows, int cols) { matrices.push(LAMatrix(vs.getNewVec(rows*cols), rows, cols)); return MId{matrices.size_()-1}; }
    MId getNewMatrix(LAVecRef v); // Initialize a (n x 1) matrix from the contents of size n vector v
    LAMatrix& operator[] (MId i) { return matrices[i.x]; }
    const LAMatrix& operator[] (MId i) const { return matrices[i.x]; }
    // Set Matrix t to contain values that are equal to those of s.  t and s need to agree on dimensions.
    void setMatrix(MId t, MId s) {
        assert(operator[](t).nRows() == operator[](s).nRows());
        assert(operator[](t).nCols() == operator[](s).nCols());
        vs[operator[](t).getCoeffs()] = vs[operator[](s).getCoeffs()];
    }
    // Return an m x n identity matrix
    MId getNewIdMatrix(int rows, int cols);

    void setIdMatrix  (MId A);

    // Multiply row ipivot by x and substract it from from i
    void submul_row   (MId A, int i, int ipivot, const opensmt::Real& x);
    // Multiply column jpivot by x and add it to column j
    void addmul_column(MId A, int j, int jpivot, const opensmt::Real& x);
    // multiply row ipivot by x and add it to row i
    void addmul_row   (MId A, int i, int ipivot, const opensmt::Real& x);
    // Multiply column jpivot byx and substract it from column j
    void submul_column(MId A, int j, int jpivot, const opensmt::Real& x);
    // Add row ipivot to row i
    void add_row      (MId A, int i, int ipivot);
    // Substract column jpivot from column j
    void sub_column   (MId A, int j, int jpivot);
    // Swap rows i1 and i2
    void swap_rows    (MId A, int i1, int i2);
    // Swap columns j1 and j2
    void swap_columns (MId A, int j1, int j2);

    // Negate the column j
    void neg_column   (MId A, int j);
    // Negate the row i
    void neg_row      (MId A, int i);
    // Transform A into a Smith matrix S such that A = X*S*U and U*V=I and X*Y=I
    void compute_snf  (MId A, MId &S, int &dim, MId &X, MId &Y, MId &U, MId &V);

    // Transform A into a Hermite matrix H such that A = H*U and U*V=I
    void compute_hnf_v1(const MId A1, MId &H, int &dim1, MId &U1, MId &V1);
    //void compute_hnf_minors(MId &H, const MId A);
    //void hnf_transform(MId &H, MId &U, const MId A);
    //void hnf(MId &H, const MId A);
    //void hnf_classical(MId H, const MId A);
    //int fz_is_zero(MId H);
    int least_in_row (MId H, int i, int jmin);
    void compute_hnf (MId &H, const MId A1);
    void compute_hhnf (MId &H, const MId A1);
    int least_in_col(MId H, int imin, int j);

    // Determine whether the linear integer equality defined by facs and c has a solution.
    // Return true and the solution in sol if yes, otherwise return false.
    //bool solve_diophantine(LAVecRef facs, opensmt::Real c, LAVecRef sol);

    LAVecRef mul_vector   (MId A, LAVecRef v);
    MId mul_matrix        (MId A, MId B);
    LAVecRef discretize   (LAVecRef v); // compute [v], i.e., round up or down to closest integer

    char* print(MId A);
};


#endif //OPENSMT_MATRIX_H
