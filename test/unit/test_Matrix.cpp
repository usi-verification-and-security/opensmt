//
// Created by prova on 24.08.18.
//
#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <Sort.h>
#include <liasolver/Matrix.h>
#include <LIALogic.h>
#include <SMTConfig.h>

using Real = opensmt::Real;

TEST(Matrix_test, cmpabs_test)
{
    Real zero;
    Real one = 1;
    Real minus_one = -1;

    ASSERT_EQ(cmpabs(zero, zero), 0);
    ASSERT_EQ(cmpabs(zero, one), -1);
    ASSERT_EQ(cmpabs(zero, minus_one), -1);

    ASSERT_EQ(cmpabs(one, zero), 1);
    ASSERT_EQ(cmpabs(one, one), 0);
    ASSERT_EQ(cmpabs(one, minus_one), 0);

    ASSERT_EQ(cmpabs(minus_one, zero), 1);
    ASSERT_EQ(cmpabs(minus_one, one), 0);
    ASSERT_EQ(cmpabs(minus_one, minus_one), 0);
}

TEST(Matrix_test, floor_div)
{
    Real x(11, 10); // 1.1
    x = x.floor();
    ASSERT_EQ(x, 1);

    Real y(-11, 10); // -1.1
    y = y.floor();
    ASSERT_EQ(y, -2);

    ASSERT_EQ(x % (-y), 1);
    ASSERT_EQ(x % y, -1);

    x = INT32_MAX;
    y = INT32_MAX;
    x *= 2;
    y *= 2;
    y = y+1;

    ASSERT_EQ(x % y, x);
    ASSERT_EQ(y % x, 1);
    Real z = -x;
    ASSERT_EQ(y % z, Real{"-4294967293"});

    Real v(-4, 3);
    v = v.floor();
    ASSERT_EQ(v.isInteger(), true);

    Real w(-3, 1);
    w = w.floor();
    ASSERT_EQ(w, -3);

    FastRational f = fastrat_fdiv_q(FastRational(-1, 1), FastRational(2, 1));
    ASSERT_EQ(f, -1);

    FastRational f2 = fastrat_fdiv_q(FastRational(1, 1), FastRational(-2, 1));
    ASSERT_EQ(f2, -1);

    Real x1 = fastrat_fdiv_q(-2936, 276);
    ASSERT_EQ(x1, -11);

    Real x2 = fastrat_fdiv_q(FastRational(-3480, 1), FastRational(-768));
    ASSERT_EQ(x2, 4);

    ASSERT_EQ(fastrat_fdiv_q(4, 4), 1);
    ASSERT_EQ(fastrat_fdiv_q(-4, -4), 1);
    ASSERT_EQ(fastrat_fdiv_q(4, -4), -1);
    ASSERT_EQ(fastrat_fdiv_q(-4, 4), -1);
    ASSERT_EQ(fastrat_fdiv_q(8, 4), 2);
    ASSERT_EQ(fastrat_fdiv_q(-8, -4), 2);
    ASSERT_EQ(fastrat_fdiv_q(8, -4), -2);
    ASSERT_EQ(fastrat_fdiv_q(-8, 4), -2);

    ASSERT_EQ(fastrat_fdiv_q(INT_MIN, 1), INT_MIN);
    ASSERT_EQ(fastrat_fdiv_q(INT_MIN, -1), FastRational(INT_MAX)+1);
    ASSERT_EQ(fastrat_fdiv_q(INT_MAX, 1), INT_MAX);
    ASSERT_EQ(fastrat_fdiv_q(INT_MAX, -1), -INT_MAX);
}

TEST(Matrix_test, vec_creation)
{
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    // INT32_MIN
    Real r {"-2147483648"};
    vec<Real> reals;
    for (int i = 0; i < 10; i++) {
        reals.push(Real(i));
    }
    LAVecRef vr = vecStore.getNewVec(reals);
    for (int i = 1; i <= va[vr].size(); i++) {
        ASSERT_EQ(va[vr][i], i-1);
    }

    LAVecRef vr2 = vecStore.getNewVec(10);
    va[vr2] = va[vr];

    for (int i = 1; i <= va[vr2].size(); i++)
        ASSERT_EQ(va[vr2][i], va[vr][i]);

    LAMatrixStore ms(vecStore);
    MId m = ms.getNewMatrix(2,2);
    ASSERT_EQ(ms[m].nRows(), 2);
    ASSERT_EQ(ms[m].nCols(), 2);

    MId m2 = ms.getNewMatrix(2,2);
    ms.setMatrix(m2, m);

    MId idmx = ms.getNewIdMatrix(2, 2);
    for (int i = 1; i <= 2; i++) {
        for (int j = 1; j <= 2; j++) {
            if (i == j)
                ASSERT_EQ(ms.MM(idmx, i, j), 1);
            else
                ASSERT_EQ(ms.MM(idmx, i, j), 0);
        }
    }

    MId diag = ms.getNewIdMatrix(2, 2);
    ms.swap_rows(diag, 1, 2);
    ASSERT_EQ(ms.MM(diag, 1, 1), 0);
    ASSERT_EQ(ms.MM(diag, 1, 2), 1);
    ASSERT_EQ(ms.MM(diag, 2, 1), 1);
    ASSERT_EQ(ms.MM(diag, 2, 2), 0);
    ms.swap_columns(diag, 1, 2);
    ASSERT_EQ(ms.MM(diag, 1, 1), 1);
    ASSERT_EQ(ms.MM(diag, 1, 2), 0);
    ASSERT_EQ(ms.MM(diag, 2, 1), 0);
    ASSERT_EQ(ms.MM(diag, 2, 2), 1);

    ms.neg_column(diag, 1);
    ASSERT_EQ(ms.MM(diag, 1, 1), -1);
    ASSERT_EQ(ms.MM(diag, 1, 2), 0);
    ASSERT_EQ(ms.MM(diag, 2, 1), 0);
    ASSERT_EQ(ms.MM(diag, 2, 2), 1);

    ms.neg_row(diag, 2);
    ASSERT_EQ(ms.MM(diag, 1, 1), -1);
    ASSERT_EQ(ms.MM(diag, 1, 2), 0);
    ASSERT_EQ(ms.MM(diag, 2, 1), 0);
    ASSERT_EQ(ms.MM(diag, 2, 2), -1);

    ms.setIdMatrix(diag);
    ASSERT_EQ(ms.MM(diag, 1, 1), 1);
    ASSERT_EQ(ms.MM(diag, 1, 2), 0);
    ASSERT_EQ(ms.MM(diag, 2, 1), 0);
    ASSERT_EQ(ms.MM(diag, 2, 2), 1);
}

TEST(Matrix_test, smith_matrix1) {
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId U = ms.getNewMatrix(3, 3);
    //  2  4   4
    // -6  6  12
    // 10 -4 -16
    ms.MM(U, 1, 1) = 2;
    ms.MM(U, 1, 2) = 4;
    ms.MM(U, 1, 3) = 4;

    ms.MM(U, 2, 1) = -6;
    ms.MM(U, 2, 2) = 6;
    ms.MM(U, 2, 3) = 12;

    ms.MM(U, 3, 1) = 10;
    ms.MM(U, 3, 2) = -4;
    ms.MM(U, 3, 3) = -16;

    MId L = ms.getNewMatrix(3, 3);
    MId R = ms.getNewMatrix(3, 3);
    MId Li = ms.getNewMatrix(3, 3);
    MId Ri = ms.getNewMatrix(3, 3);

    MId S = ms.getNewMatrix(3, 3);

    int dim;

    ms.compute_snf(U, S, dim, L, Li, R, Ri);
    printf("The snf matrix:\n%s\n", ms.print(S));
    /* int diag[] = {2, 6, 12};
     for (int i = 1; i <= 3; i++) {
         for (int j = 1; j <= 3; j++) {
             if (i != j)
                 ASSERT_EQ(ms.MM(S, i, j), 0);
             else
                 ASSERT_EQ(ms.MM(S, i, j), diag[i - 1]);
         }
     }*/
}

TEST(Matrix_test, smith_matrix111) {
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId U = ms.getNewMatrix(4, 4);
    //  -6 111 -36 6
    // 5 -672 210 74
    // 0 -255 81 24
    // -7 255 -81 -10
    ms.MM(U, 1, 1) = -6;
    ms.MM(U, 1, 2) = 111;
    ms.MM(U, 1, 3) = -36;
    ms.MM(U, 1, 4) = 6;

    ms.MM(U, 2, 1) = 5;
    ms.MM(U, 2, 2) = -672;
    ms.MM(U, 2, 3) = 210;
    ms.MM(U, 2, 4) = 74;

    ms.MM(U, 3, 1) = 0;
    ms.MM(U, 3, 2) = -255;
    ms.MM(U, 3, 3) = 81;
    ms.MM(U, 3, 4) = 24;

    ms.MM(U, 4, 1) = -7;
    ms.MM(U, 4, 2) = 255;
    ms.MM(U, 4, 3) = -81;
    ms.MM(U, 4, 4) = -10;

    MId L = ms.getNewMatrix(4, 4);
    MId R = ms.getNewMatrix(4, 4);
    MId Li = ms.getNewMatrix(4, 4);
    MId Ri = ms.getNewMatrix(4, 4);

    MId S = ms.getNewMatrix(4, 4);

    // 1 3 21 0 in diagonal should be for S

    int dim;

    ms.compute_snf(U, S, dim, L, Li, R, Ri);
    printf("The snf matrix:\n%s\n", ms.print(S));
    /* int diag[] = {2, 6, 12};
     for (int i = 1; i <= 3; i++) {
         for (int j = 1; j <= 3; j++) {
             if (i != j)
                 ASSERT_EQ(ms.MM(S, i, j), 0);
             else
                 ASSERT_EQ(ms.MM(S, i, j), diag[i - 1]);
         }
     }*/
}

TEST(Matrix_test, smith_matrix2) {
    // [[-2561 1265 2517 -3732 1490 1769 1203 -4213 2948 -3189 129 -129 1475 4601 -1635 768 -3204 3619 337 657]
    // [0 0 0 0 0 0 0 -1 0 0 0 0 0 0 0 0 0 0 0 0]]
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId T = ms.getNewMatrix(20, 2);
    ms.MM(T, 1, 1) = -2561;
    ms.MM(T, 2, 1) = 1265;
    ms.MM(T, 3, 1) = 2517;
    ms.MM(T, 4, 1) = -3732;
    ms.MM(T, 5, 1) = 1490;
    ms.MM(T, 6, 1) = 1769;
    ms.MM(T, 7, 1) = 1203;
    ms.MM(T, 8, 1) = -4213;
    ms.MM(T, 9, 1) = 2948;
    ms.MM(T, 10, 1) = -3189;
    ms.MM(T, 11, 1) = 129;
    ms.MM(T, 12, 1) = -129;
    ms.MM(T, 13, 1) = 1475;
    ms.MM(T, 14, 1) = 4601;
    ms.MM(T, 15, 1) = -1635;
    ms.MM(T, 16, 1) = 768;
    ms.MM(T, 17, 1) = -3204;
    ms.MM(T, 18, 1) = 3619;
    ms.MM(T, 19, 1) = 337;
    ms.MM(T, 20, 1) = 657;

    ms.MM(T, 1, 2) = 0;
    ms.MM(T, 2, 2) = 0;
    ms.MM(T, 3, 2) = 0;
    ms.MM(T, 4, 2) = 0;
    ms.MM(T, 5, 2) = 0;
    ms.MM(T, 6, 2) = 0;
    ms.MM(T, 7, 2) = 0;
    ms.MM(T, 8, 2) = 1;
    ms.MM(T, 9, 2) = 0;
    ms.MM(T, 10, 2) = 0;
    ms.MM(T, 11, 2) = 0;
    ms.MM(T, 12, 2) = 0;
    ms.MM(T, 13, 2) = 0;
    ms.MM(T, 14, 2) = 0;
    ms.MM(T, 15, 2) = 0;
    ms.MM(T, 16, 2) = 0;
    ms.MM(T, 17, 2) = 0;
    ms.MM(T, 18, 2) = 0;
    ms.MM(T, 19, 2) = 0;
    ms.MM(T, 20, 2) = 0;

    MId S2 = ms.getNewMatrix(20, 2);
    MId L2 = ms.getNewMatrix(20, 20);
    MId L2i = ms.getNewMatrix(20, 20);
    MId R2 = ms.getNewMatrix(2, 2);
    MId R2i = ms.getNewMatrix(2, 2);
    int dim;
    ms.compute_snf(T, S2, dim, L2, L2i, R2, R2i);
    printf("snf matrix:\n%s\n", ms.print(S2));
}

TEST(Matrix_test, smith_matrix3) {

    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId T3 = ms.getNewMatrix(21, 1);
    ms.MM(T3, 1, 1)  = -2936;
    ms.MM(T3, 2, 1)  = 768;
    ms.MM(T3, 3, 1)  = 344;
    ms.MM(T3, 4, 1)  = -688;
    ms.MM(T3, 5, 1)  = 3192;
    ms.MM(T3, 6, 1)  = -4092;
    ms.MM(T3, 7, 1)  = 1848;
    ms.MM(T3, 8, 1)  = -2640;
    ms.MM(T3, 9, 1)  = -3872;
    ms.MM(T3, 10, 1) = 1988;
    ms.MM(T3, 11, 1) = 2340;
    ms.MM(T3, 12, 1) = -3317;
    ms.MM(T3, 13, 1) = 276;
    ms.MM(T3, 14, 1) = -2188;
    ms.MM(T3, 15, 1) = 1836;
    ms.MM(T3, 16, 1) = -912;
    ms.MM(T3, 17, 1) = -1225;
    ms.MM(T3, 18, 1) = 1788;
    ms.MM(T3, 19, 1) = -1988;
    ms.MM(T3, 20, 1) = 1588;
    ms.MM(T3, 21, 1) = 448;
    MId S3 = ms.getNewMatrix(21, 1);
    MId L3 = ms.getNewMatrix(21, 21);
    MId L3i = ms.getNewMatrix(21, 21);
    MId R3 = ms.getNewMatrix(1, 1);
    MId R3i = ms.getNewMatrix(1, 1);
    int dim;
    ms.compute_snf(T3, S3, dim, L3, L3i, R3, R3i);
    printf("snf matrix:\n%s\n", ms.print(S3));
}

TEST(Matrix_test, smith_matrix4) {

    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    const int N = 20;
    MId T3 = ms.getNewMatrix(N, 1);
    int vals[N] = {-3480, -1956, -768, -1732, 1700, 15748, 800, 4280, 5276, -963, -3576, 5324, 23800, -5324, -2820, 1732, 3532, -1796, -868, 3269};
    for (int i = 1; i <= N; i++)
        ms.MM(T3, i, 1) = vals[i-1];

    MId S3 = ms.getNewMatrix(N, 1);
    MId L3 = ms.getNewMatrix(N, N);
    MId L3i = ms.getNewMatrix(N, N);
    MId R3 = ms.getNewMatrix(1, 1);
    MId R3i = ms.getNewMatrix(1, 1);
    int dim;
    ms.compute_snf(T3, S3, dim, L3, L3i, R3, R3i);
    printf("snf matrix:\n%s\n", ms.print(S3));
}

TEST(Matrix_test, matrix_mult) {
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId A = ms.getNewMatrix(2, 2);
    ms.MM(A, 1, 1) = 1;
    ms.MM(A, 2, 1) = 2;
    ms.MM(A, 1, 2) = 3;
    ms.MM(A, 2, 2) = 4;

    MId R = ms.mul_matrix(A, A);
    ASSERT_EQ(ms.MM(R, 1, 1), 7);
    ASSERT_EQ(ms.MM(R, 2, 1), 10);
    ASSERT_EQ(ms.MM(R, 1, 2), 15);
    ASSERT_EQ(ms.MM(R, 2, 2), 22);

    MId B = ms.getNewMatrix(2, 3);
    MId C = ms.getNewMatrix(3, 2);
    ms.MM(B, 1, 1) = 1;
    ms.MM(B, 2, 1) = 2;
    ms.MM(B, 1, 2) = 3;
    ms.MM(B, 2, 2) = 4;
    ms.MM(B, 1, 3) = 5;
    ms.MM(B, 2, 3) = 6;
    ms.MM(C, 1, 1) = 1;
    ms.MM(C, 2, 1) = 2;
    ms.MM(C, 3, 1) = 3;
    ms.MM(C, 1, 2) = 4;
    ms.MM(C, 2, 2) = 5;
    ms.MM(C, 3, 2) = 6;
    MId R2 = ms.mul_matrix(B, C);
    char* R2_str = ms.print(R2);
    printf("The matrix:\n%s\n", R2_str);
    free(R2_str);
    ASSERT_EQ(ms.MM(R2, 1, 1), 22);
    ASSERT_EQ(ms.MM(R2, 2, 1), 28);
    ASSERT_EQ(ms.MM(R2, 1, 2), 49);
    ASSERT_EQ(ms.MM(R2, 2, 2), 64);

    LAVecRef x = vecStore.getNewVec({1, 2, 3});
    LAVecRef v = ms.mul_vector(B, x);
    ASSERT_EQ(vecStore[v][1], 22);
    ASSERT_EQ(vecStore[v][2], 28);
}

TEST(Matrix_test, discretize)
{
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vs(va, logic);
    LAMatrixStore ms(vs);
    LAVecRef v = vs.getNewVec(13);
    vs[v][1] = 0;
    vs[v][2] = FastRational("1/10");
    vs[v][3] = FastRational("-1/10");
    vs[v][4] = FastRational("-1/2");
    vs[v][5] = FastRational("-7/10");
    vs[v][6] = FastRational("7/10");
    vs[v][7] = FastRational("11/10");
    vs[v][8] = FastRational("-11/10");
    vs[v][9] = FastRational("2147483648/2147483647");
    vs[v][10] = FastRational("-2147483649/2147483648");
    vs[v][11] = FastRational("1/2147483648");
    vs[v][12] = FastRational("-1/2147483649");

    LAVecRef u = ms.discretize(v);
    ASSERT_EQ(vs[u][1], 0);
    ASSERT_EQ(vs[u][2], 0);
    ASSERT_EQ(vs[u][3], 0);
    ASSERT_EQ(vs[u][4], 0);
    ASSERT_EQ(vs[u][5], -1);
    ASSERT_EQ(vs[u][6], 1);
    ASSERT_EQ(vs[u][7], 1);
    ASSERT_EQ(vs[u][8], -1);
    ASSERT_EQ(vs[u][9], 1);
    ASSERT_EQ(vs[u][10], -1);
    ASSERT_EQ(vs[u][11], 0);
    ASSERT_EQ(vs[u][12], 0);
}

TEST(Matrix_test, non_square)
{
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId U = ms.getNewMatrix(2,3); // Should be 2 columns, 3 rows
    ms.MM(U, 1, 1) = 11;
    ms.MM(U, 2, 1) = 21;
    ms.MM(U, 1, 2) = 12;
    ms.MM(U, 2, 2) = 22;
    ms.MM(U, 1, 3) = 13;
    ms.MM(U, 2, 3) = 23;
    char* m_str = ms.print(U);
    printf("The matrix:\n%s\n", m_str);
    free(m_str);
}

TEST(gcd_test, gcd)
{
    FastRational p1(7177);
    FastRational p2(7817);
    FastRational p3(173);

    FastRational q1 = p1*p3;
    FastRational q2 = p2*p3;

    ASSERT_EQ(gcd(p1, p2), 1);
    ASSERT_EQ(gcd(p1, p3), 1);
    ASSERT_EQ(gcd(p2, p3), 1);
    ASSERT_EQ(gcd(q1, q2), p3);
    ASSERT_EQ(gcd(q2, q1), p3);

    FastRational p4(7919);
    FastRational p5(7907);
    FastRational q3 = p1*p2*p4;
    FastRational q4 = p1*p2*p5;

    ASSERT_EQ(gcd(q3, q4), p1*p2);

    FastRational r1 = q3*q4;
    FastRational r2 = q3*q4*p3;
    ASSERT_EQ(gcd(r1, r2), q3*q4);
}

TEST(lcm_test, lcm)
{
    FastRational p1(2);
    FastRational p2(6);

    ASSERT_EQ(lcm(p1, p2), 6);
    ASSERT_EQ(lcm(p2, p1), 6);

    FastRational p3(7177);
    FastRational p4(7817);
    FastRational p5(7919);
    FastRational p6(7907);

    ASSERT_EQ(lcm(p3, p4), p3*p4);


    FastRational q1 = p3*p4;
    FastRational q2 = p5*p6;

    ASSERT_EQ(lcm(q1, q2), p3*p4*p5*p6);
    FastRational p7(4);
    FastRational p8("2147483648");
    FastRational q3 = p7*p8;
    ASSERT_EQ(lcm(p7, p8), p8);
    ASSERT_EQ(lcm(p8, p7), p8);


}

TEST(lcm_test, lcm_list)
{
    FastRational p1(2, 5);
    FastRational p2(3, 7);
    FastRational p3(5, 11);

    vec<FastRational> l = {p1, p2, p3};
    FastRational r = get_multiplicand(l);
    ASSERT_EQ(r, 385);
}


TEST(Matrix_test, hermite_matrix1) {
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId U = ms.getNewMatrix(4, 4);
    //  3 3 1 4
    //  0 1 0 0
    //  0 0 19 16
    //  0 0 0 3

    //HNF

    //3 0 1 1
    //0 1 0 0
    //0 0 19 1
    //0 0 0 3
    ms.MM(U, 1, 1) = 3;
    ms.MM(U, 1, 2) = 3;
    ms.MM(U, 1, 3) = 1;
    ms.MM(U, 1, 4) = 4;

    ms.MM(U, 2, 1) = 0;
    ms.MM(U, 2, 2) = 1;
    ms.MM(U, 2, 3) = 0;
    ms.MM(U, 2, 4) = 0;

    ms.MM(U, 3, 1) = 0;
    ms.MM(U, 3, 2) = 0;
    ms.MM(U, 3, 3) = 19;
    ms.MM(U, 3, 4) = 16;

    ms.MM(U, 4, 1) = 0;
    ms.MM(U, 4, 2) = 0;
    ms.MM(U, 4, 3) = 0;
    ms.MM(U, 4, 4) = 3;

    //MId R = ms.getNewMatrix(4, 4);
    //MId Ri = ms.getNewMatrix(4, 4);

    MId H = ms.getNewMatrix(4, 4);

    //int dim;

    ms.compute_hnf(H, U);
    printf("The hnf matrix:\n%s\n", ms.print(H));

}

TEST(Matrix_test, hermite_matrix2) {
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId U = ms.getNewMatrix(4, 4);
    //  0 -1 1 0
    //  -2 3 2 1
    //  -6 -1 -2 0
    //  4 -2 -2 10

    //HNF

    //2 0 1 11
    //0 1 5 12
    //0 0 6 12
    //0 0 0 33

    ms.MM(U, 1, 1) = 0;
    ms.MM(U, 1, 2) = -1;
    ms.MM(U, 1, 3) = 1;
    ms.MM(U, 1, 4) = 0;

    ms.MM(U, 2, 1) = -2;
    ms.MM(U, 2, 2) = 3;
    ms.MM(U, 2, 3) = 2;
    ms.MM(U, 2, 4) = 1;

    ms.MM(U, 3, 1) = -6;
    ms.MM(U, 3, 2) = -1;
    ms.MM(U, 3, 3) = -2;
    ms.MM(U, 3, 4) = 0;

    ms.MM(U, 4, 1) = 4;
    ms.MM(U, 4, 2) = -2;
    ms.MM(U, 4, 3) = -2;
    ms.MM(U, 4, 4) = 10;

    MId H = ms.getNewMatrix(4, 4);

    //int dim;

    ms.compute_hnf(H, U);
    printf("The hnf matrix:\n%s\n", ms.print(H));

}

/*
TEST(Matrix_test, hermite_matrix3) {
    LAVecAllocator va;
    SMTConfig config;
    LIALogic logic(config);
    LAVecStore vecStore(va, logic);
    LAMatrixStore ms(vecStore);
    MId U = ms.getNewMatrix(3, 4);
    //  2 3 6 2
    //  5 6 1 6
    //  8 3 1 1

    //HNF

    //1 0 50 -11
    //0 3 28 -2
    //0 0 61 -13


    ms.MM(U, 1, 1) = 2;
    ms.MM(U, 1, 2) = 3;
    ms.MM(U, 1, 3) = 6;
    ms.MM(U, 1, 4) = 2;

    ms.MM(U, 2, 1) = 5;
    ms.MM(U, 2, 2) = 6;
    ms.MM(U, 2, 3) = 1;
    ms.MM(U, 2, 4) = 6;

    ms.MM(U, 3, 1) = 8;
    ms.MM(U, 3, 2) = 3;
    ms.MM(U, 3, 3) = 1;
    ms.MM(U, 3, 4) = 1;


    MId H = ms.getNewMatrix(3, 4);

    //int dim;

    ms.compute_hnf(H, U);
    printf("The hnf matrix:\n%s\n", ms.print(H));

}*/
