#include "Number.h"

namespace opensmt {
FlexibleNumber::FlexibleNumber(char const * str) : FlexibleNumber(Real{str}) {
    tryTurnToInteger();
}
} // namespace opensmt
