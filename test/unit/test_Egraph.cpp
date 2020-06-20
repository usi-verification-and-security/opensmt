//
// Created by Martin Blicha on 2018-12-31.
//

#include <gtest/gtest.h>
#include "Egraph.h"

TEST(UseVector_test, testAdd){
    UseVector uv;
    ERef x{0};
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    EXPECT_TRUE(uv[0].isValid());
}

TEST(UseVector_test, testAddAndRemove){
    UseVector uv;
    ERef x{0};
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    uv.clearEntryAt(0);
    ASSERT_EQ(uv.size(), 0);
    auto entry =  uv[0];
    EXPECT_TRUE(entry.isFree());
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    entry = uv[0];
    EXPECT_TRUE(entry.isValid());
}

TEST(UseVector_test, testAddAndRemoveMultiple){
    UseVector uv;
    ERef x{0};
    uv.addParent(x);
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 2);
    uv.clearEntryAt(0);
    ASSERT_EQ(uv.size(), 1);
    uv.clearEntryAt(1);
    ASSERT_EQ(uv.size(), 0);
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    uv.addParent(x);
    ASSERT_EQ(uv.size(), 2);
}

TEST(UseVector_test, testWriteRead){
    UseVector uv;
    ERef x{137};
    auto index = uv.addParent(x);
    ASSERT_EQ(uv.size(), 1);
    auto entry = uv[index];
    ASSERT_EQ(UseVector::entryToERef(entry), x);
    entry.mark();
    entry.unmark();
    ASSERT_EQ(UseVector::entryToERef(entry), x);
}


