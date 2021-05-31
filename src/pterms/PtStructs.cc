#include <PtStructs.h>


bool PtAsgn::operator== (const PtAsgn& other) const { return tr == other.tr && sgn == other.sgn; }
bool PtAsgn::operator!= (const PtAsgn& other) const { return !(*this == other); }
bool PtAsgn::operator< (const PtAsgn& other) const { return tr < other.tr || (tr == other.tr && toInt(sgn) < toInt(other.sgn)); }


uint32_t PtAsgnHash::operator () (const PtAsgn& s) const {
    return ((uint32_t)s.tr.x << 2) + toInt(s.sgn);
}



bool LessThan_PTRef::operator () (PTRef& x, PTRef& y) { return x.x < y.x; }


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
