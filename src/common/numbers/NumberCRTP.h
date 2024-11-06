//
// Created by Tomas Kolarik on 05.11.24
//

#ifndef OPENSMT_NUMBERCRTP_H
#define OPENSMT_NUMBERCRTP_H

#include <common/CRTP.h>

#include <iosfwd>
#include <utility>

namespace opensmt {
template<typename T>
class NumberCRTP : public CRTP<T> {
public:
    struct Hash {
        //- std::size_t operator()(NumberCRTP const & x) const { return x.asDerived().hash(); }
        std::size_t operator()(NumberCRTP const & x) const { return 0; }
    };
};

template<typename T>
T abs(NumberCRTP<T> const & x) {
    //- !!!
    return {};
}

template<typename T>
std::ostream & operator<<(std::ostream & os, NumberCRTP<T> const & x) {
    //- !!!
    return os;
}
} // namespace opensmt

//- namespace std {
//- template<typename T>
//- struct hash<opensmt::NumberCRTP<T>> : opensmt::NumberCRTP<T>::Hash {};
//- } // namespace std

#endif // OPENSMT_NUMBERCRTP_H
