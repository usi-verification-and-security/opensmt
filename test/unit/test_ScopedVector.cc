/*
* Copyright (c) 2025, Tomas Kolarik <tomaqa@gmail.com>
*
*  SPDX-License-Identifier: MIT
*
*/

#include <gtest/gtest.h>
#include <common/ScopedVector.h>

namespace opensmt {

class Test : public ::testing::Test {
public:
    Test() {}

    bool compare(std::vector<int> const & v) const {
        return compareTp(svector, v);
    }

    bool compareTopScope(std::vector<int> const & v) const {
        return compareTp(svector.topScope(), v);
    }

    bool compareScope(std::size_t idx, std::vector<int> const & v) const {
        return compareTp(svector.scope(idx), v);
    }

protected:
    bool compareTp(auto const & sv, std::vector<int> const & v) const {
        if (sv.size() != v.size()) { return false; }
        auto vIt = v.begin();
        for (auto & sve : sv) {
            auto & ve = *vIt++;
            if (sve != ve) { return false; }
        }

        auto * vptr = v.data();
        auto * svptr = sv.data();
        for (size_t i = 0; i < sv.size(); ++i) {
            auto & sve = *svptr++;
            auto & ve = *vptr++;
            if (sve != ve) { return false; }
        }

        return true;
    }

    ScopedVector<int> svector;
};

TEST_F(Test, test_ScopeVector1) {
    ASSERT_TRUE(compare({}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 1);
    svector.push(1);
    ASSERT_TRUE(compare({1}));
    ASSERT_TRUE(compareTopScope({1}));
    ASSERT_TRUE(compareScope(0, {1}));
    ASSERT_EQ(svector.scopeCount(), 1);
    svector.push(2);
    ASSERT_TRUE(compare({1, 2}));
    ASSERT_TRUE(compareTopScope({1, 2}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 1);

    svector.pushScope();
    ASSERT_TRUE(compare({1, 2}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(1, {}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);
    svector.push(3);
    ASSERT_TRUE(compare({1, 2, 3}));
    ASSERT_TRUE(compareTopScope({3}));
    ASSERT_TRUE(compareScope(1, {3}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);
    svector.push(4);
    ASSERT_TRUE(compare({1, 2, 3, 4}));
    ASSERT_TRUE(compareTopScope({3, 4}));
    ASSERT_TRUE(compareScope(1, {3, 4}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);

    svector.pushScope();
    ASSERT_TRUE(compare({1, 2, 3, 4}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(2, {}));
    ASSERT_TRUE(compareScope(1, {3, 4}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 3);
    svector.popScope();
    ASSERT_TRUE(compare({1, 2, 3, 4}));
    ASSERT_TRUE(compareTopScope({3, 4}));
    ASSERT_TRUE(compareScope(1, {3, 4}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);

    svector.pushScope();
    ASSERT_TRUE(compare({1, 2, 3, 4}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(2, {}));
    ASSERT_TRUE(compareScope(1, {3, 4}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 3);
    svector.push(5);
    ASSERT_TRUE(compare({1, 2, 3, 4, 5}));
    ASSERT_TRUE(compareTopScope({5}));
    ASSERT_TRUE(compareScope(2, {5}));
    ASSERT_TRUE(compareScope(1, {3, 4}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 3);
    svector.popScope();
    ASSERT_TRUE(compare({1, 2, 3, 4}));
    ASSERT_TRUE(compareTopScope({3, 4}));
    ASSERT_TRUE(compareScope(1, {3, 4}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);

    svector.popScope();
    ASSERT_TRUE(compare({1, 2}));
    ASSERT_TRUE(compareTopScope({1, 2}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 1);
    svector.pushScope();
    ASSERT_TRUE(compare({1, 2}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(1, {}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);
    svector.push(6);
    ASSERT_TRUE(compare({1, 2, 6}));
    ASSERT_TRUE(compareTopScope({6}));
    ASSERT_TRUE(compareScope(1, {6}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 2);

    svector.popScope();
    ASSERT_TRUE(compare({1, 2}));
    ASSERT_TRUE(compareTopScope({1, 2}));
    ASSERT_TRUE(compareScope(0, {1, 2}));
    ASSERT_EQ(svector.scopeCount(), 1);

    svector.clear();
    ASSERT_TRUE(compare({}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 1);
}

TEST_F(Test, test_ScopeVector2) {
    svector.pushScope();
    ASSERT_TRUE(compare({}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(1, {}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 2);
    svector.push(1);
    ASSERT_TRUE(compare({1}));
    ASSERT_TRUE(compareTopScope({1}));
    ASSERT_TRUE(compareScope(1, {1}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 2);
    svector.push(2);
    ASSERT_TRUE(compare({1, 2}));
    ASSERT_TRUE(compareTopScope({1, 2}));
    ASSERT_TRUE(compareScope(1, {1, 2}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 2);

    svector.popScope();
    ASSERT_TRUE(compare({}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 1);

    svector.clear();
    ASSERT_TRUE(compare({}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 1);
}

TEST_F(Test, test_ScopeVector3) {
    svector.push(11);
    ASSERT_TRUE(compare({11}));
    ASSERT_TRUE(compareTopScope({11}));
    ASSERT_TRUE(compareScope(0, {11}));
    ASSERT_EQ(svector.scopeCount(), 1);
    svector.push(22);
    ASSERT_TRUE(compare({11, 22}));
    ASSERT_TRUE(compareTopScope({11, 22}));
    ASSERT_TRUE(compareScope(0, {11, 22}));
    ASSERT_EQ(svector.scopeCount(), 1);

    svector.pushScope();
    ASSERT_TRUE(compare({11, 22}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(1, {}));
    ASSERT_TRUE(compareScope(0, {11, 22}));
    ASSERT_EQ(svector.scopeCount(), 2);
    svector.push(33);
    ASSERT_TRUE(compare({11, 22, 33}));
    ASSERT_TRUE(compareTopScope({33}));
    ASSERT_TRUE(compareScope(1, {33}));
    ASSERT_TRUE(compareScope(0, {11, 22}));
    ASSERT_EQ(svector.scopeCount(), 2);

    svector.clear();
    ASSERT_TRUE(compare({}));
    ASSERT_TRUE(compareTopScope({}));
    ASSERT_TRUE(compareScope(0, {}));
    ASSERT_EQ(svector.scopeCount(), 1);
}

}
