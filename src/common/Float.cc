#include "Float.h"

#include "OsmtApiException.h"

#include <iostream>
#include <iomanip>
#include <sstream>
#include <string>

using namespace std::literals::string_literals;

namespace opensmt {
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
            throw OsmtApiException("Expected '/' after "s + std::to_string(val) + ", got: " + std::string(str));
        }
        is >> std::noskipws >> rhs;
        if (is && is.eof()) {
            val /= rhs;
            assert(normalized(val));
            return;
        }

        throw OsmtApiException("Cannot convert to float: "s + std::string(str));
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
        os << std::setprecision(std::numeric_limits<Value>::max_digits10) << value();
    }
}
