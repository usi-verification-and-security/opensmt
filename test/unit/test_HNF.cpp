#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <Sort.h>
#include <liasolver/Matrix.h>
#include <LIALogic.h>
#include <SMTConfig.h>

class HNF_test : public ::testing::Test {
protected:
    HNF_test() : logic{config}, vecStore(va, logic), ms(vecStore) {}
    virtual void SetUp() {
    }
    SMTConfig config;
    LIALogic logic;
    LAVecAllocator va;
    LAVecStore vecStore;
    LAMatrixStore ms;

};

TEST_F(HNF_test, test_hnf1)
{
    MId U = ms.getNewMatrix(4, 4);

    int u[4][4] = {{3, 0, 0, 0},
                   {3, 1, 0, 0},
                   {1, 0, 19, 0},
                   {4, 0, 16, 3}};

    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 4; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF
    int hnf_ref[4][4] = {{3, 0, 0, 0},
                         {0, 1, 0, 0},
                         {1, 0, 19, 0},
                         {1, 0, 1, 3}};

    MId H = ms.getNewMatrix(4, 4);

    int dim;
    MId U1 = MId_Undef;
    MId V1 = MId_Undef;

    ms.compute_hnf_v1(U, H, dim, U1, V1);
    printf("The hnf matrix:\n%s\n", ms.print(H));

    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 4; j++)
            ASSERT_EQ(ms.MM(H, i+1, j+1), hnf_ref[i][j]);
}

TEST_F(HNF_test, test_hnf2) {
    MId U = ms.getNewMatrix(4, 4);

    int u[4][4] = {{0, -2, 6, 4},
                   {-1, 3, -1, -2},
                   {1, 2, -2, -2},
                   {0, 1, 0, 10}};

    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 4; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF
    int hnf_ref[4][4] = {{2, 0, 0, 0},
                         {0, 1, 0, 0},
                         {1, 5, 6, 0},
                         {11, 12, 12, 21}}; // Checked form numbertheory.org

    MId H = ms.getNewMatrix(4, 4);

    int dim;
    MId U1 = MId_Undef;
    MId V1 = MId_Undef;

    ms.compute_hnf_v1(U, H, dim, U1, V1);

    cout << "The hnf matrix: " << endl << ms.print(H) << endl;
    for (int i = 0; i < 4; i++)
        for (int j = 0; j < 4; j++)
            ASSERT_EQ(ms.MM(H, i+1, j+1), hnf_ref[i][j]);
}

TEST_F(HNF_test, test_hnf3) {
    int rows = 4;
    int cols = 3;
    MId U = ms.getNewMatrix(rows, cols);
    int u[4][3] = {{2, 5, 8},
                   {3, 6, 3},
                   {6, 1, 1},
                   {2, 6, 1}};

    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF

    int hnf_ref[4][3] = {{1, 0, 0},
                         {0, 3, 0},
                         {50, 28, 61},
                         {-11, -2, -13}};

    MId H = ms.getNewMatrix(rows, cols);

    int dim;
    MId U1 = MId_Undef;
    MId V1 = MId_Undef;
    ms.compute_hnf_v1(U, H, dim, U1, V1);
    cout << "The hnf matrix:" << endl << ms.print(H) << endl;
    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            ASSERT_EQ(ms.MM(H, i+1, j+1), hnf_ref[i][j]);
}


