#include "Float.h"

#include <common/ApiException.h>
#include <common/StringConv.h>

#include <iostream>
#include <iomanip>
#include <sstream>
#include <string>

namespace opensmt {
    using namespace std::literals::string_literals;

    Float::Float(char const * str) {
        auto & val = value();

        std::istringstream is(str);
        is >> val;
        if (is && is.eof()) {
            assert(normalized(val));
            return;
        }

        Value rhs;
        char c = is.get();
        assert(is);
        if (c != '/') {
            throw ApiException("Expected '/' after "s + std::to_string(val) + ", got: " + std::string(str));
        }
        is >> std::noskipws >> rhs;
        if (is && is.eof()) {
            val /= rhs;
            assert(normalized(val));
            return;
        }

        throw ApiException("Cannot convert to float: "s + std::string(str));
    }

    std::string Float::get_str() const {
        std::ostringstream os;
        print(os);
        auto str = os.str();
        //- assert(value() !=  0.0 || str == "0");
        //- assert(value() != -0.0 || str == "0");
        assert(!isZero() || str == "0");
        return str;
    }

    void Float::print(std::ostream & os) const {
        //- assert(value() != -0.0 || isZero());
        //- if (isZero()) {
        //-     os << "0";
        //-     return;
        //- }
        //- !!!
        //- else if (value() == 0.5) os << "1/2";
        //- std::cerr << value() << std::endl;
        assert(!isZero() || !std::signbit(value()));
        //- os << std::fixed << std::setprecision(20) << value();

        // does not print rational representation which later may miss mapping the same constants on each other ...
        //- os << std::setprecision(std::numeric_limits<Value>::max_digits10) << value();

        std::ostringstream auxOss;
        auxOss << std::fixed << std::setprecision(std::numeric_limits<Value>::max_digits10) << value();
        char * rationalString;
        stringToRational(rationalString, auxOss.str().c_str());
        os << rationalString;
        free(rationalString);
    }
}
