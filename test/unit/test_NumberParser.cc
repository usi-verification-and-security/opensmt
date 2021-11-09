//
// Created by Antti on 16.09.21.
//

#include <gtest/gtest.h>
#include <StringConv.h>

using namespace opensmt;

class NumberParserTest : public ::testing::Test {
public:
    NumberParserTest() {}
};

TEST_F(NumberParserTest, test_RealCheck) {
    std::vector<std::string> pos_cases =
            {"1", "-1", ".1", "-.1", "0.1", "-0.1", "0", "-0",
             "1/2", "-1/2", "0.1/2", ".1/2", "-.1/2", "1/.2", "-1/.2",
             "-0.1/2", "0.1/0.2", "-0.1/0.2", ".1/.2", "-.1/.2", "123",
             "123/234", "123.456", "123.456/234.567"};
    std::vector<std::string> neg_cases =
            {"", "a", "1a", "/2", "1/", "1/-2"};

    std::cout << "Postitive cases:" << std::endl;
    for (auto s : pos_cases) {
        std::cout << " - " << s << std::endl;
        ASSERT_TRUE(isRealString(s.data()));
    }

    std::cout << "Negative cases:" << std::endl;
    for (auto s: neg_cases) {
        std::cout << " - " << s << std::endl;
        ASSERT_FALSE(isRealString(s.data()));
    }
}

TEST_F(NumberParserTest, test_IntCheck) {
    std::vector<std::string> pos_cases =
            {"1", "-1", "0", "-0", "123", "-123"};
    std::vector<std::string> neg_cases =
            {"", "a", "1a", "/2", "1/", "1/-2", ".1", "-.1", "0.1", "-0.1",
             "1/2", "-1/2", "0.1/2", ".1/2", "-.1/2", "1/.2", "-1/.2",
             "-0.1/2", "0.1/0.2", "-0.1/0.2", ".1/.2", "-.1/.2"};

    std::cout << "Postitive cases:" << std::endl;
    for (auto s : pos_cases) {
        std::cout << " - " << s << std::endl;
        ASSERT_TRUE(isIntString(s.data()));
    }

    std::cout << "Negative cases:" << std::endl;
    for (auto s: neg_cases) {
        std::cout << " - " << s << std::endl;
        ASSERT_FALSE(isIntString(s.data()));
    }
}