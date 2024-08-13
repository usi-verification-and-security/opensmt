#include "PtStructs.h"

namespace opensmt {
uint32_t PtAsgnHash::operator()(PtAsgn const & s) const {
    return ((uint32_t)s.tr.x << 2) + toInt(s.sgn);
}
} // namespace opensmt
