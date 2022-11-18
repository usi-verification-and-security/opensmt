#include <PtStructs.h>

uint32_t PtAsgnHash::operator () (const PtAsgn& s) const {
    return ((uint32_t)s.tr.x << 2) + toInt(s.sgn);
}



ValPair::~ValPair() {
    if (val != NULL)
        free(val);
}

ValPair::ValPair(const ValPair& other) {
    tr = other.tr;
    if (other.val != NULL)
        val = strdup(other.val);
    else val = NULL;
}
const ValPair& ValPair::operator= (const ValPair& other) {
    tr = other.tr;
    if (other.val != NULL)
        val = strdup(other.val);
    else val = NULL;
    return *this;
}
bool ValPair::operator== (const ValPair& other) const { return tr == other.tr && val == other.val; }
bool ValPair::operator!= (const ValPair& other) const { return tr != other.tr || val != other.val; }
