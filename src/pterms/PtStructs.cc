#include <PtStructs.h>

uint32_t PtAsgnHash::operator () (const PtAsgn& s) const {
    return ((uint32_t)s.tr.x << 2) + toInt(s.sgn);
}