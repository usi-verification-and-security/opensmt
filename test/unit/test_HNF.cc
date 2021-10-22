#include <gtest/gtest.h>
#include <Real.h>
#include <stdlib.h>
#include <Vec.h>
#include <Sort.h>
#include <lasolver/Matrix.h>
#include <ArithLogic.h>

class HNF_test : public ::testing::Test {
protected:
    HNF_test() : logic{ArithLogic::ArithType::LIA}, vecStore(va, logic), ms(vecStore) {}
    virtual void SetUp() {
    }
    ArithLogic logic;
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

    int u[4][4] = {{0, -2, -6, 4},
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
                         {11, 12, 12, 33}}; // Checked form numbertheory.org

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

TEST_F(HNF_test, test_hnf4) {
    int rows = 4;
    int cols = 4;
    MId U = ms.getNewMatrix(rows, cols);

    int u[4][4] = {{1, 2, -6, -6},
                   {2, -5, -3, 7},
                   {-4, -3, 0, 0},
                   {1, -3, 5, -8}};

    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF

    int hnf_ref[4][4] = {{1, 0, 0, 0},
                         {0, 1, 0, 0},
                         {0, 0, 1, 0},
                         {335, 286, 1663, 2873}};

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

TEST_F(HNF_test, test_hnf5) {
    int rows = 3;
    int cols = 3;
    MId U = ms.getNewMatrix(rows, cols);

    int u[3][3] = {{9, -36, 30},
                   {-36, 192, -180},
                   {30, -180, 180}};


    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF

    int hnf_ref[3][3] = {{3, 0, 0},
                         {0, 12, 0},
                         {30, 0, 60}};

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

/*

TEST_F(HNF_test, test_hnf6) {
int rows = 4;
int cols = 4;
MId U = ms.getNewMatrix(rows, cols);

int u[4][4] = {{-25, 15, -52, -16},
               {36, -10, 26, -21},
               {-44, 35, -66, 98},
               {20, -12, 72, -30}};

for (int i = 0; i < rows; i++)
for (int j = 0; j < cols; j++)
ms.MM(U, i+1, j+1) = u[i][j];

//HNF

int hnf_ref[4][4] = {{1, 0, 0, 0},
                     {0, 1, 0, 0},
                     {0, 0, 2, 0},
                     {148191, 959683, 327841, 1083310}};

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

TEST_F(HNF_test, test_hnf7) {
int rows = 5;
int cols = 5;
MId U = ms.getNewMatrix(rows, cols);

int u[5][5] = {{25, -300, 1050, -1400, 630},
               {-300, 4800, -18900, 26880, -12600},
               {1050, -18900, 79380, -117600, 56700},
               {-1400, 26880, -117600, 179200, -88200},
               {630, -12600, 56700, -88200, 44100}};


for (int i = 0; i < rows; i++)
for (int j = 0; j < cols; j++)
ms.MM(U, i+1, j+1) = u[i][j];

//HNF

int hnf_ref[5][5] = {{5, 0, 0, 0, 0},
                     {0, 60, 0, 0, 0},
                     {-210, 0, 420, 0, 0},
                     {-280, 0, 0, 840, 0},
                     {630, 0, 0, 0, 2520}};

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
*/

TEST_F(HNF_test, test_hnf8) {
    int rows = 4;
    int cols = 5;
    MId U = ms.getNewMatrix(rows, cols);

    int u[4][5] = {{9,  6,  0, -8,  0},
                   {-5, -8,  0,  0,  0},
                   {0,  0,  0,  4,  0},
                   {0,  0,  0, -5,  0}};


    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF

    int hnf_ref[4][5] = {{1, 0, 0, 0, 0},
                         {1, 2, 0, 0, 0},
                         {28, 36, 84, 0, 0},
                         {-35, -45, -105, 0, 0}};

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

TEST_F(HNF_test, test_hnf9) {
    int rows = 6;
    int cols = 4;
    MId U = ms.getNewMatrix(rows, cols);

    int u[6][4] = {{-5, -2,  7,  1},
                   {8,  8,  -5,  -1},
                   {-3, -2, -8, 6},
                   {-9, -2, 4, 0},
                   {5, 8, 3, 8},
                   {5, 5, -4, -3}};


    for (int i = 0; i < rows; i++)
        for (int j = 0; j < cols; j++)
            ms.MM(U, i+1, j+1) = u[i][j];

    //HNF

    int hnf_ref[6][4] = {{1, 0, 0, 0},
                         {0, 1, 0, 0},
                         {3, 1, 4, 0},
                         {237, 103, 352, 486},
                         {-299, -130, -450, -627},
                         {90, 40, 135, 188}};

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


