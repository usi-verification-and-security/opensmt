//
// Created by prova on 25.07.18.
//

#ifndef OPENSMT_TRESULT_H
#define OPENSMT_TRESULT_H

enum TResVal {trv_SAT, trv_UNSAT, trv_UNKNOWN, trv_UNDEF};
class TRes
{
private:
    TResVal val;
public:
    TRes(TResVal v) : val(v) {}
    TRes(const TRes& o) : val(o.val) {}
    TRes& operator= (const TRes& o) { val = o.val; return *this; }
    bool operator== (const TRes& o) { return val == o.val; }
    bool operator!= (const TRes& o) { return val != o.val; }
};

static class TRes TR_SAT     = TRes{trv_SAT};
static class TRes TR_UNSAT   = TRes{trv_UNSAT};
static class TRes TR_UNKNOWN = TRes{trv_UNKNOWN};
static class TRes TR_UNDEF   = TRes{trv_UNDEF};

#endif //OPENSMT_TRESULT_H
