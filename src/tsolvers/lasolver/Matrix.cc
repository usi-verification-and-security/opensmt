//
// Created by prova on 24.08.18.
//

#include "Matrix.h"

#include <iostream>

LAVecRef
LAVecStore::getNewVec(std::vector<opensmt::Real>&& ps, const opensmt::Real& den)
{
    LAVecRef vr = lva.alloc(std::move(ps), den);
    return vr;
}

char*
LAVecStore::print(LAVecRef vr)
{
    char *str;
    int res = asprintf(&str, "[\n");
    assert(res >= 0); (void)res;
    for (int i = 1; i <= operator[](vr).size(); i++) {
        char* tmp;
        std::string s = operator[](vr)[i].get_str();
        int res = asprintf(&tmp, "%s%s \n", str, s.c_str());
        assert(res >= 0); (void)res;
        free(str);
        str = tmp;
    }
    char *tmp;
    res = asprintf(&tmp, "%s]\n", str);
    assert(res >= 0); (void)res;
    free(str);
    str = tmp;
    return str;
}

opensmt::Real&
LAMatrixStore::MM(MId mid, int row, int col)
{
    LAMatrix& m = operator[](mid);
    int ncols = m.nCols();
    assert(row >= 1 && col >= 1);
    assert(row <= m.nRows() && col <= ncols);
    return vs[m.getCoeffs()][ncols*(row-1) + col-1 + 1]; // Vectors are indexed from 1 ... n
}

MId
LAMatrixStore::getNewIdMatrix(int rows, int cols)
{
    int i, max = cols < rows ? rows : cols;
    MId mid = getNewMatrix(rows, cols);
    for (i = 1; i <= max; i++)
        MM(mid, i, i) = 1;
    return mid;
}

void
LAMatrixStore::setIdMatrix(MId A)
{
    LAMatrix& AM = operator[](A);
    for (int i = 1; i <= AM.nRows(); i ++)
        for (int j = 1; j <= AM.nCols(); j++)
            MM(A, i, j) = (i == j) ? 1 : 0;
}

void
LAMatrixStore::submul_row(MId A, int i, int ipivot, const opensmt::Real& x)
{
#ifdef ENABLE_MATRIX_TRACE
    string s = x.get_str();
    printf("submul_row i = %d, ipivot = %d, x = %s\n", i, ipivot, s.c_str());
#endif
    assert(x.isInteger());
    assert(i != ipivot);
    if (A == MId_Undef) return;
    for (int j = 1; j <= operator[](A).nCols(); j++) {
        MM(A, i, j) -= x * MM(A, ipivot, j);
    }
}


void
LAMatrixStore::addmul_column(MId A, int j, int jpivot, const opensmt::Real& x)
{
#ifdef ENABLE_MATRIX_TRACE
    string s = x.get_str();
    printf("addmul_column j = %d, jpivot = %d, x = %s\n", j, jpivot, s.c_str());
#endif
    assert(x.isInteger());
    assert(j != jpivot);
    if (A == MId_Undef) return;
    for (int i = 1; i <= operator[](A).nRows(); i++)
        MM(A, i, j) += x*MM(A, i, jpivot);
}

void
LAMatrixStore::addmul_row(MId A, int i, int ipivot, const opensmt::Real& x)
{
    std::string s = x.get_str();
#ifdef ENABLE_MATRIX_TRACE
    printf("addmul_row i = %d, ipivot = %d, x = %s\n", i, ipivot, s.c_str());
#endif
    assert(x.isInteger());
    assert(i != ipivot);
    if (A == MId_Undef) return;
    for (int j = 1; j <= operator[](A).nCols(); j++)
        MM(A, i, j) += x*MM(A, ipivot, j);
}

void
LAMatrixStore::submul_column(MId A, int j, int jpivot, const opensmt::Real& x)
{
#ifdef ENABLE_MATRIX_TRACE
    string s = x.get_str();
    printf("submul_column j = %d, jpivot = %d, x = %s\n", j, jpivot, s.c_str());
#endif
    assert(x.isInteger());
    assert(j != jpivot);
    if (A == MId_Undef) return;

#ifdef ENABLE_MATRIX_TRACE
    printf("Before: ");
    for (int i = 1; i <= operator[](A).nRows(); i++)
        printf("%s%s", i == 1 ? "" : " ", MM(A, i, j).get_str().c_str());
    printf("\n");
#endif
    for (int i = 1; i <= operator[](A).nRows(); i++) {
#ifdef ENABLE_MATRIX_TRACE
        cout << MM(A, i, j).get_str() << " -= " << x.get_str() << " * " << MM(A, i, jpivot).get_str() << endl;
#endif
        MM(A, i, j) -= x * MM(A, i, jpivot);
#ifdef ENABLE_MATRIX_TRACE
        cout << " => " << MM(A, i, j).get_str() << endl;
#endif
    }
#ifdef ENABLE_MATRIX_TRACE
    printf("After: ");
    for (int i = 1; i <= operator[](A).nRows(); i++)
        printf("%s%s", i == 1 ? "" : " ", MM(A, i, j).get_str().c_str());
    printf("\n");
#endif
}

void
LAMatrixStore::add_row(MId A, int i, int ipivot)
{
    assert (i != ipivot);
#ifdef ENABLE_MATRIX_TRACE
    printf("add_row %d, %d\n", i, ipivot);
#endif
    if (A == MId_Undef) return;
    for (int j = 1; j <= operator[](A).nCols(); j++)
        MM(A, i, j) += MM(A, ipivot, j);
}

void
LAMatrixStore::swap_rows (MId A, int i1, int i2)
{
#ifdef ENABLE_MATRIX_TRACE
    printf("swap_rows %d, %d\n", i1, i2);
#endif
    if (A == MId_Undef) return;
    for (int j = 1; j <= operator[](A).nCols(); j++)
        std::swap(MM(A, i1, j), MM(A, i2, j));
}

void
LAMatrixStore::swap_columns(MId A, int j1, int j2)
{
#ifdef ENABLE_MATRIX_TRACE
    printf("swap_cols %d, %d\n", j1, j2);
#endif
    if (A == MId_Undef) return;
    for (int i = 1; i <= operator[](A).nRows(); i++)
        std::swap(MM(A, i, j1), MM(A, i, j2));
}

void
LAMatrixStore::neg_column(MId A, int j)
{
#ifdef ENABLE_MATRIX_TRACE
    printf("neg_column %d\n", j);
#endif
    if (A == MId_Undef) return;
    for (int i = 1; i <= operator[](A).nRows(); i++)
        MM(A, i, j).negate();
}

void
LAMatrixStore::neg_row(MId A, int i)
{
#ifdef ENABLE_MATRIX_TRACE
    printf("neg_row %d\n", i);
#endif
    if (A == MId_Undef) return;
    for (int j = 1; j <= operator[](A).nCols(); j++)
        MM(A, i, j).negate();
}

void
LAMatrixStore::sub_column(MId A, int j, int jpivot)
{
#ifdef ENABLE_MATRIX_TRACE
    printf("sub_column %d, %d\n", j, jpivot);
#endif
    assert(j != jpivot);
    if (A == MId_Undef) return;
    LAMatrix& Am = operator[](A);
    for (int i = 1; i <= Am.nRows(); i++)
        MM(A, i, j) -= MM(A, i, jpivot);
}

// return the column number j>=jmin of the least absolute coefficient H[i,j].
// return 0 if H[i,j]=0 for any j>=jmin
int LAMatrixStore::least_in_row(MId H, int i, int jmin) {
    int pos = 0;
    opensmt::Real least;
    LAMatrix& Hm = operator[](H);
    assert(jmin <= Hm.nCols());
    for (int j = Hm.nCols(); j > jmin; j--) {
        if (MM(H, i, j) == 0)
            continue;
        if (pos != 0) {
            if (cmpabs(MM(H, i, j), least) <= 0) {
                pos = j;
                least = MM(H, i, j);
            }
        }
        else {
            pos = j;
            least = MM(H, i, j);
        }
    }
    return pos;
}

// return the row number imin of the least absolute coefficient in the column H[i,j]
//
//        //i0 ← { i ∈ [k, n] : ai, j = min{|ai, j| : i ∈[k, n]}};
//        //abs of coeffs
//        //if col = 1 then we look from 1 onwards, if two from two onwards and so on
//        //if least coeff 0 then continue to next column
int
LAMatrixStore::least_in_col(MId H, int imin, int j)
{
#ifdef ENABLE_MATRIX_TRACE
    printf("least %d, %d\n", imin, j);
#endif
    int jmin;
    bool found;
    opensmt::Real valmin;
    LAMatrix& Hm = operator[](H);

    // The position of the minimum element in absolute value
    // not equal to 0 is denoted by (imin, jmin), and is H[imin, jmin] = valmin
    //if col = 1 then we look from 1 onwards, if two from two onwards and so on, that is why i = imin

    found = false;
    for (int i = imin; i <= Hm.nRows(); i++) { //i = 1
        if (MM(H, i, j) == 0)
            continue;

        if (!found) {
            found = true;
            imin = i;
            jmin = j;
            valmin = MM(H, imin, jmin);
//#ifdef ENABLE_MATRIX_TRACE
            //          string s = valmin.get_str();
            // printf("valmin", s.c_str());
//#endif
        } else if (cmpabs(valmin, MM(H, i, j)) > 0) {
            imin = i;
            jmin = j;
            valmin = MM(H, imin, jmin);
        }
    }
    return imin;
}


//  Transform the matrix U into a Smith matrix S
//  and compute four matrices  R, Ri, L and Li for which it holds:
//    - R.Ri = I, Ri.R = I, L.Li = I and Li.L = I where I is the identity matrix
//    - U = L.S.R
//  In the following k is the number of rows
//  and n is the number of columns.
//  For the moment in our application the rows are the equqlities and columns are variables.
//
//  U is k * n
//  S is k * n
//
//  Code assumes that
//
//    - The size of L is k*k
//    - The size of Li is k*k
//    - The size of R is n*n
//    - The size of Ri is n*n
//    - The size of U is k*n
//
//  If R  == MId_Undef then it will not be computed
//  If Ri == MId_Undef then it will not be computed
//  If L  == MId_Undef then it will not be computed
//  If Li == MId_Undef then it will not be computed
//  Dim is equal to the rank of the Smith matrix S of U
//
void
LAMatrixStore::compute_snf(MId U, MId &S, int &dim, MId &L, MId &Li, MId &R, MId &Ri)
{
    int imin = 0;
    int jmin = 0;
    bool found = false;
    opensmt::Real x, valmin;
    auto const& store = *this; (void) store;
    LAMatrix& Sm = operator[](S);
    if (R != MId_Undef) {
        assert(store[R].nCols() == store[R].nRows());
        assert(store[R].nRows() == store[U].nCols());

    }
    if (Ri != MId_Undef) {
        assert(store[Ri].nRows() == store[Ri].nCols());
        assert(store[Ri].nRows() == store[R].nCols());

    }
    if (L != MId_Undef) {
        assert(store[L].nCols() == store[L].nRows());
        assert(store[L].nCols() == store[U].nRows());

    }
    if (Li != MId_Undef) {
        assert(store[Li].nRows() == store[Li].nCols());
        assert(store[Li].nRows() == store[L].nRows());
    }

    //std::cout << " Rows U" << Um.nRows() << " Cols U " << Um.nCols() << " Rows S" << Sm.nRows() << " Cols S " << Sm.nCols() << "\n";

    if (U != S)
        setMatrix(S, U);

    if (R != MId_Undef)
        setIdMatrix(R);

    if (Ri != MId_Undef)
        setIdMatrix(Ri);

    if (L != MId_Undef)
        setIdMatrix(L);

    if (Li != MId_Undef)
        setIdMatrix(Li);


    int p;
    for (p = 1; (p <= Sm.nCols()) && (p <= Sm.nRows()); p++)
    {
        // The position of the minimum element in absolute value
        // not equal to 0 is denoted by (imin, jmin), and is S[imin, jmin] = valmin
        // imin = 1; // Is this correct?
        // in = 1; // Ditto?
        found = false;
        for (int j = p; j <= Sm.nCols(); j++) {
            for (int i = p; i <= Sm.nRows(); i++) {
                if (MM(S, i, j) != 0) {
                    if (!found) {
                        found = true;
                        imin = i;
                        jmin = j;
                        valmin = MM(S, imin, jmin);
                    } else if (cmpabs(valmin, MM(S, i, j)) > 0) {
                        imin = i;
                        jmin = j;
                        valmin = MM(S, imin, jmin);
                    }
                }
            }
        }

        if (!found)
            break;

        while (true)
        {
            // Try to put a 0 on column jmin
            found = false;
            for (int i = p; (i <= Sm.nRows()) && !found ; i++) {
                if ((i != imin) && (MM(S, i, jmin) != 0)) {
                    x = fastrat_fdiv_q(MM(S, i, jmin), valmin);
                    // Substract row i from row imin x times
                    submul_row(S, i, imin, x);
                    addmul_column(L, imin, i, x);
                    submul_row(Li, i, imin, x);
                    // Try to find a smaller value
                    for (int j = p; j <= Sm.nCols(); j++) {
                        if (MM(S, i, j) != 0 && cmpabs(valmin, MM(S, i, j)) > 0) {
                            imin = i;
                            jmin = j;
                            valmin = MM(S, imin, jmin);
                            found = true;
                        }
                    }
                }
            }

            if (found)
                continue;

            // We try to put 0 on row imin
            assert(!found);
            for (int j = p; (j <= Sm.nCols()) && (!found) ; j++) {
                if ((j != jmin) && (MM(S, imin, j) != 0)) {
                    x = fastrat_fdiv_q(MM(S, imin, j), valmin);
                    // Substract column j from column jmin x times
                    submul_column(S, j, jmin, x);
                    addmul_row(R, jmin, j, x);
                    submul_column (Ri, j, jmin, x);
                    // Try to find a smaller value
                    for (int i = p ; i <= Sm.nRows(); i++) {
                        if (MM(S, i, j) != 0 && (cmpabs(valmin, MM(S, i, j)) > 0)) {
                            imin = i;
                            jmin = j;
                            valmin = MM(S, imin, jmin);
                            found = true;
                        }
                    }
                }
            }
            if (found)
                continue;

            // Try to find a value that cannot be divided by valmin
            assert(!found);
            for (int j = p; (j <= Sm.nCols()) && !found; j++) {
                for (int i = p; (i <= Sm.nRows()) && !found; i++) {
                    if ((i != imin) && (j != jmin)) {
                        x = MM(S, i, j) % valmin;
                        if (x != 0) {
                            assert(i != imin);
                            assert(j != jmin);
                            // Add to row i the row imin
                            add_row(S, i, imin);
                            sub_column(L, imin, i);
                            add_row(Li, i, imin);
                            x = fastrat_fdiv_q(MM(S, i, j), valmin);
                            // Subtract from column j the column jmin x times
                            submul_column(S, j, jmin, x);
                            addmul_row(R, jmin, j, x);
                            submul_column(Ri, j, jmin, x);
                            imin = i;
                            jmin = j;
                            valmin = MM(S, imin, jmin);
                            found = true;
                        }
                    }
                }
            }
            if (found)
                continue;
            else
                break;
        }
        // Swap rows imin and p
        if (imin != p)
        {
            swap_rows(S, imin, p);
            swap_columns(L, imin, p);
            swap_rows(Li, imin, p);
            imin = p;
        }

        // We swap columns jmin and p
        if (jmin != p)
        {
            swap_columns(S, jmin, p);
            swap_rows(R, jmin, p);
            swap_columns(Ri, jmin, p);
            jmin = p;
        }

        // Enforce valmin to be positive
        if (valmin < 0)
        {
            valmin.negate();
            neg_column(S, p);
            if (R != MId_Undef)
                neg_row(R, p);
            if (Ri != MId_Undef)
                neg_column(Ri, p);
        }
    }

    dim=p-1;
}



///PS: HERE I implement computation of Hermite Normal Form///
//  Transform the matrix U into a Hermite matrix H
//  and compute two matrices  R and Ri for which it holds:
//    - R.Ri = I, Ri.R = I where I is the identity matrix
//    - U = H.R
//     H = UA, thus U can be any k*n, A also can be k*n - U and A can have diff numbers of row and columns
//  In the following k is the number of rows
//  and n is the number of columns.
//  For the moment in our application the rows are the inequalities and columns are variables.

 //Main comment: The size of H must be the same as that of A and U must be square of compatible
 // dimension (having the same number of rows as A).
//
//  U is k * n (row x column)
// A is n * m (row should be equal to U column and column can be any)
//  H is k * k
//  If R  == MId_Undef then it will not be computed
//  If Ri == MId_Undef then it will not be computed
//  Dim is equal to the rank of the Hermite matrix H of U
//
void
LAMatrixStore::compute_hnf_v1(const MId U1, MId &H, int &dim1, MId &R1, MId &Ri1)
{
    int curcol;
    opensmt::Real pivot, x;

    LAMatrix& Hm = operator[](H);
    LAMatrix& U1m = operator[](U1);
    if (R1 != MId_Undef) {
        assert(operator[](R1).nRows() == U1m.nRows());
    }

    if (H != U1)
        setMatrix(H, U1);
    if (R1 != MId_Undef)
        setIdMatrix(R1);
    if (Ri1 != MId_Undef)
        setIdMatrix(Ri1);

    curcol=1;
    for (int p = 1; p <= U1m.nRows(); p++)
    {
        int j;
        while ((j = least_in_row(H, p, curcol)) !=0) //here we wanna say while least in row is not zero do something
        {
            if (j != curcol)
            {
                swap_columns(H, j, curcol);
                if (R1 != MId_Undef)
                    swap_rows(R1, j, curcol);
                if (Ri1 != MId_Undef)
                    swap_columns (Ri1, j, curcol);
                j = curcol;
            }
            pivot = MM(H, p, j);
            if (pivot < 0)
            {
                pivot.negate();
                neg_column(H, j);
                assert(([this, Hm, H, j]()->bool { bool val = true; for (int i = 0; i < Hm.nRows(); i++) { val &= MM(H, i+1, j).isInteger(); } return val; })());
                if (R1 != MId_Undef)
                    neg_row(R1, j);
                if (Ri1 != MId_Undef)
                    neg_column(Ri1, j);
            }

            for (int l = j + 1; l <= Hm.nCols(); l++)
            {
                if (MM(H, p, l) == 0)
                    continue;
                x = fastrat_fdiv_q(MM(H, p, l), pivot);
                assert(x.isInteger());
                //We subtract from the column l, x times the column j
                assert(([this, Hm, H, l]()->bool { bool val = true; for (int i = 0; i < Hm.nRows(); i++) { val &= MM(H, i+1, l).isInteger(); } return val; })());
                submul_column(H, l, j, x);
                assert(([this, Hm, H, l]()->bool { bool val = true; for (int i = 0; i < Hm.nRows(); i++) { val &= MM(H, i+1, l).isInteger(); } return val; })());
                //We add to the line l, x times the line j [To check]
                if (R1 != MId_Undef)
                    addmul_row(R1, j, l, x);
                if (Ri1 != MId_Undef)
                    submul_column(Ri1, l, j, x);
            }
        }

        pivot = MM(H, p, curcol);
        if (pivot < 0)
        {
            pivot.negate();
            neg_column (H, curcol);
            if (R1 != MId_Undef)
                neg_row(R1, curcol);
            if (Ri1 != MId_Undef)
                neg_column(Ri1, curcol);
        }

        if (pivot != 0)
        {
            for (int l = 1; l <= curcol-1; l++)
            {
                if (MM(H, p, l) == 0)
                    continue;
                x = fastrat_fdiv_q(MM(H, p, l), pivot);
                // We subtract from column l, x times the column curcol
                submul_column(H, l, curcol , x);
                // We add to line l, x times line curcol to check
                addmul_row(R1, curcol, l, x);
                submul_column(Ri1, l, curcol, x);
            }
            curcol++;
            if (curcol > U1m.nCols())
                break;
        }
    }
    curcol--;
    dim1 = curcol;
}



/// Here is the end of computation of Hermite Normal Form ///


///compute hnf from pdf

void
LAMatrixStore::compute_hnf(MId &H, const MId A){//, int &dim) {//maybe no need for dim and p

    LAMatrix &Hm = operator[](H);

    if (H != A)
        setMatrix(H, A);

    int k=1, i0;
    opensmt::Real b, t, q, f, x, y;

    //int p;
    //for (p = 1; (p <= Am.nCols()) && (p <= Am.nRows()); p++) {

    for (int j = 1; j <= Hm.nCols() && k<=Hm.nRows(); j++) {
        //k = 1;
        // Choose Pivot
        i0 = least_in_col(H, k, j); //i0 should be equal to the number of the row that min val resides

        printf("leastrowvalue %d\n", i0);

        if (i0 > k) {
            //Exchange row Ak with row Ai0;
            swap_rows(H, k, i0);

        }
        if (MM(H, k, j) < 0) {
            //Ak ← −Ak;
            neg_row(H, k);
            //std::cout << " first for loop finished" << "\n";
        }
        // Reduce Rows
        //b ← ak, j;
        b = MM(H, k,j); //error with k, as MM(mid, row, col) and row maybe 3 but col 4, and in this case k = 4, which breaks assersion

        std::cout << " b equal to " << b << "\n";

        if (b == 0)
            continue;
        else {
            for (int i = k + 1; i <= Hm.nRows(); i++) {
                //q ← ⌊ai, j / b⌉; //nearest integer or exact div? i checked exact division normal div
                f = MM(H, i, j) / b; //Note: rounding to nearest integer does not work
                std::cout << " q1 equal to " << q << "\n";
                if(!(f.isInteger())){
                    //get separate den of f (call it x) and cislitel of f (call it y)
                    x = f.get_den();
                    y = f.get_num();

                    for (int l = 1; l <= Hm.nCols(); j++) {
                        MM(H, i, l) = x * MM(H, i, l) - y * MM(H, k, l);
                    }

                } else {

                    //Ai ← Ai − q × Ak;
                    //MM(H, i, j) -= q * MM(H, k, j);
                    submul_row(H, i, k, f);
                }
            }

            for (int i = k - 1; i > 0; i--) {
                // q ← ⌊ai,j/b⌋; q = flooor of the division 1/6 and 5.6 shoud give approx 0, if in neg then -1
                t = MM(H, i, j) / b; //correct this with floor
                q = t.floor();
                //Ai ← Ai − q × Ak;
                //MM(H, i, j) -= q * MM(H, k, j);
                submul_row(H, i, k, q);
            }
        }
        k = k + 1;

    }
}

///end of compute hnf from pdf

/*
void
LAMatrixStore::compute_hhnf(MId &H, const MId A){//, int &dim) {//maybe no need for dim and p

    LAMatrix &Hm = operator[](H);
    LAMatrix &Am = operator[](A);

    LAVecRef d = vs.getNewVec(Am.nCols());

    if (H != A)
        setMatrix(H, A);

    int k=1, i0;
    opensmt::Real b, t, s, q, f, u, v, d, y;

    //int p;
    //for (p = 1; (p <= Am.nCols()) && (p <= Am.nRows()); p++) {

    for (int j = 1; j <= Hm.nCols() && k<=Hm.nRows(); j++) {
        if (MM(H, k, j) < 0) {
            //Ak ← −Ak;
            neg_row(H, k);
            //std::cout << " first for loop finished" << "\n";
        }
        // Reduce Rows
        //b ← ak, j;
        b = MM(H, k,j); //error with k, as MM(mid, row, col) and row maybe 3 but col 4, and in this case k = 4, which breaks assersion

        std::cout << " b equal to " << b << "\n";

        if (b == 0)
            continue;
        else {
            for (int i = k + 1; i <= Hm.nRows(); i++) {
                if (MM(H,i,j) != 0){
                    // Euclidean Step
                    //Compute (d, u, v) such that uak,j + vai,j = d = gcd(ak,j , ai,j );
                    u*MM(H,k,j) + v*MM(H,i,j) = d;
                    d = gcd(MM(H,k,j), MM(H,i,j));

                    //Ai ← (ak,j /d)Ai − (ai,j /d)Ak ;
                    t = (MM(H,k,j) / d)*MM(H,i,j);
                    //std::cout << " t equal to " << t << "\n";
                    s = (MM(H,i,j) / d)*MM(H,k,j);
                    MM(H,i,j) = t - s;
                    //Ak ←B;
                    //B ← uAk + vAi;
                    //d = u*MM(H,k,j) + v*MM(H,i,j);
                    //vecStore[d][i+1]
                }
            }
            for (int i = k - 1; i > 0; i--) {
                // q ← ⌊ai,j/b⌋; q = flooor of the division 1/6 and 5.6 shoud give approx 0, if in neg then -1
                y = MM(H, i, j) / b; //correct this with floor
                q = y.floor();
                //Ai ← Ai − q × Ak;
                //MM(H, i, j) -= q * MM(H, k, j);
                submul_row(H, i, k, q);
            }
        }
        k = k+1;
    }
}
*/


///TEST HNF MINORS

//The size of H must be the same as that of A
//Computes an integer matrix H such that H is the unique (row) Hermite normal form of A

/*
void
LAMatrixStore::compute_hnf_minors(MId &H, const MId A)
{
    long j, j2, i, k, l, m, n;
    opensmt::Real u, v, d, r2d, r1d, q, b;

    LAMatrix& Hm = operator[](H);
    LAMatrix& Am = operator[](A);

    m = Am.nRows();
    n = Am.nCols();

    // put the kth principal minor in HNF
    for (k = 0, l = m-1; k < n; k++) //k=0 it was, l = m - 1
    {
        for (j = 0; j < k; j++) //j was 0
        {
            gcd(MM(H, j, j), MM(H, k, j)); //check fmpz_xgcd(d, u, v, fmpz_mat_entry(H, j, j), fmpz_mat_entry(H, k, j));
            r1d = divexact(MM(H, j, j), d); //fmpz_divexact
            std::cout << "Result of exact div" << r1d << std::endl;

            r2d = divexact(MM(H, k, j), d); //fmpz_divexact
            for (j2 = j; j2 < n; j2++)
            {
                b = u * MM(H, j, j2); //fmpz_mul(b, u, MM(H, j, j2));
                b += v*MM(H, k, j2); //fmpz_addmul(b, v, MM(H, k, j2));
                MM(H, k, j2) = r1d * MM(H, k, j2); //fmpz_mul(MM(H, k, j2), r1d, MM(H, k, j2));
                MM(H, k, j2) -= r2d*MM(H, j, j2); //fmpz_submul(MM(H, k, j2), r2d, MM(H, j, j2));
                MM(H, j, j2) = b;
            }
        }
        // if H_k,k is zero we swap row k for some other row (starting with the last)
        if (MM(H, k, k) == 0) //double check fmpz_is_zero
        {
            swap_rows(H, k, l);
            l--;
            k--;
            continue;
        }
        // ensure H_k,k is positive
        if (MM(H, k, k) < 0)
        {
            for (j = k; j < n; j++)
            {
                MM(H, k, j).negate();
            }
        }
        //reduce above diagonal elements of each row i
        for (i = k - 1; i >= 0; i--) //i>=0 it was
        {
            for (j = i + 1; j <= k; j++)
            {
                q = fastrat_fdiv_q(MM(H, i, j), MM(H, j, j));
                for (j2 = j; j2 < n; j2++)
                {
                    MM(H, i, j2) -= q*MM(H, j, j2); //fmpz_submul(MM(H, i, j2), q, MM(H, j, j2));

                }
            }
        }
        l = m-1; //l = m-1
    }

    //reduce final rows
    for (k = n; k < m; k++)
    {
        for (j = 1; j < n; j++) //j=0
        {
            gcd(MM(H, j, j), MM(H, k, j)); //check fmpz_xgcd(d, u, v, MM(H, j, j), MM(H, k, j)
            r1d = divexact(MM(H, j, j), d); //fmpz_divexact
            r2d = divexact(MM(H, k, j), d); //fmpz_divexact
            for (j2 = j; j2 < n; j2++)
            {
                b = u*MM(H, j, j2); //fmpz_mul(b, u, MM(H, j, j2));
                b += v*MM(H, k, j2); //fmpz_addmul(b, v, MM(H, k, j2));
                MM(H, k, j2) = r1d * MM(H, k, j2); //fmpz_mul(MM(H, k, j2), r1d, MM(H, k, j2));
                MM(H, k, j2) -= r2d*MM(H, j, j2); //fmpz_submul(MM(H, k, j2), r2d, MM(H, j, j2));
                MM(H, j, j2) = b;
            }
        }
        //reduce above diagonal elements of each row i
        for (i = n-1; i >= 0; i--) // j = n - 1, i >= 0
        {
            for (j = i + 1; j < n; j++)
            {
                q = fastrat_fdiv_q(MM(H, i, j), MM(H, j, j));
                for (j2 = j; j2 < n; j2++)
                {
                    MM(H, i, j2) -= q*MM(H, j, j2); //fmpz_submul(MM(H, i, j2), q, MM(H, j, j2));
                }
            }
        }
    }

}
*/


///HNF classical

/*
//col_finished = fmpz_is_zero(MM(H, i, j));

int LAMatrixStore::fz_is_zero(FastRational& n){

    assert(n.isInteger());

    int col_finished;
    LAMatrix& HM = operator[](H);
    for (int i = 1; i <= HM.nRows(); i ++)
        for (int j = 1; j <= HM.nCols(); j++)
            if (MM(H, i, j) == 0) {
                col_finished = 1;
            } else {
                col_finished = 0;
            }
}
*/

/*
void LAMatrixStore::hnf_classical(MId H, const MId A)
{
    int i, i0, j, j2, k, l, m, n;
    opensmt::Real min, q;
    bool col_finished;

    LAMatrix& Hm = operator[](H);
    LAMatrix& Am = operator[](A);

    m = Am.nRows();
    n = Am.nCols();

    for (j = 1, k = 1, l = (n - m) * (n > m); n - j != l; j++, k++) //you may want to set to 1
    {
        //int col_finished = 1;
        col_finished = true; //or false
        for (i = k + 1; (i <= m) && col_finished; i++) //<
            //col_finished = fmpz_is_zero(MM(H, i, j));


            col_finished = (MM(H, i, j) == 0 ? true : false);

            //col_finished = fz_is_zero(MM(H, i, j));

        if (col_finished)
        {
            if (MM(H, k, j) < 0)
            {
                for (j2 = j; j2 <= n; j2++)
                    MM(H, k, j2).negate();
            }
            if (MM(H, i, j) == 0)//no need for is zero
            {
                k--;
                if (l > 0)
                    l--;
            }
            else
            {
                // reduce first entries of column j with row k
                for (i = 1; i < k; i++)
                {
                    q = fastrat_fdiv_q(MM(H, i, j), MM(H, k, j));
                    for (j2 = j; j2 <= n; j2++)
                    {
                        MM(H, i, j2) -= q * MM(H, k, j2); //fmpz_submul
                    }
                }
            }
        }
        else
        {
            i0 = 0;
            // locate non-zero entry in column j below k with lowest absolute value
            for (i = k + 1; i <= m; i++)
            {
                if (MM(H, i, j) == 0)
                    continue;
                if ((min == 0) || cmpabs(MM(H, i, j), min) < 0) //fmpz_cmpabs
                {
                    i0 = i;
                    min = abs(MM(H, i, j));//fmpz_abs
                }
            }
            // move the row found to row k
            if (i0 > k)
                swap_rows(H, i0, k);

            if (MM(H, k, j) < 0)
            {
                for (j2 = j; j2 <= n; j2++)
                {
                    MM(H, k, j2).negate();
                }
            }
            // reduce lower entries of column j with row k
            for (i = k + 1; i <= m; i++)
            {
                q = fastrat_fdiv_q(MM(H, i, j), MM(H, k, j));
                for (j2 = j; j2 < n; j2++)
                {
                    MM(H, i, j2) -= q * MM(H, k, j2);
                }
            }
            // don't move to the next column yet
            j--;
            k--;
        }
    }
}
*/

///END of HNF classical

MId
LAMatrixStore::getNewMatrix(LAVecRef v)
{
    MId A = getNewMatrix(vs[v].size(), 1);
    vs[operator[](A).getCoeffs()] = vs[v];
    return A;
}

MId
LAMatrixStore::mul_matrix(const MId A, const MId B)
{
    assert(operator[](A).nCols() == operator[](B).nRows());
//    MId R = getNewMatrix(operator[](A).nCols(), operator[](B).nRows());
    MId R = getNewMatrix(operator[](A).nRows(), operator[](B).nCols());
    for (int i = 1; i <= operator[](A).nRows(); i++) {
        for (int j = 1; j <= operator[](B).nCols(); j++) {
            MM(R, i, j) = 0;
            for (int k = 1; k <= operator[](A).nCols(); k++) {
                MM(R, i, j) += MM(A, i, k) * MM(B, k, j);
            }
        }
    }
    return R;
}

LAVecRef
LAMatrixStore::mul_vector(MId A, LAVecRef v)
{
    MId vm = getNewMatrix(v);
    MId res = mul_matrix(A, vm);
    return operator[](res).getCoeffs();
}

LAVecRef
LAMatrixStore::discretize(const LAVecRef v)
{
    LAVecRef v_r = vs.getNewVec(vs[v].size());

    for (int i = 1; i <= vs[v].size(); i++)
        vs[v_r][i] = fastrat_round_to_int(vs[v][i]);

    return v_r;
}

char*
LAMatrixStore::print(MId A)
{
    int nRows = operator[](A).nRows();
    int nCols = operator[](A).nCols();
    char* buf = (char*)malloc(1);
    char* buf_new;

    buf[0] = '\0';
    for (int i = 1; i <= nRows; i++) {
        char* col_buf = (char*)malloc(1);
        col_buf[0] = '\0';
        for (int j = 1; j <= nCols; j++) {
            int res = asprintf(&buf_new, "%s%s%s", col_buf, MM(A, i, j).get_str().c_str(), j < nCols ? " " : "");
            assert(res >= 0); (void)res;
            free(col_buf);
            col_buf = buf_new;
        }
        int res = asprintf(&buf_new, "%s%s[%s]%s", buf, i == 1 ? "" : " ", col_buf, i < nRows ? "\n" : "");
        assert(res >= 0); (void)res;
        free(col_buf);
        free(buf);
        buf = buf_new;
    }
    int res = asprintf(&buf_new, "[%s]", buf);
    assert(res >= 0); (void)res;
    free(buf);
    return buf_new;
}
