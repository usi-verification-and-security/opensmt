#ifndef OPENSMT_CRTP_H
#define OPENSMT_CRTP_H

namespace opensmt {
template<typename T>
class CRTP {
protected:
    friend T;

    using Derived = T;

    CRTP() = default;
    ~CRTP() = default;
    CRTP(CRTP const &) = default;
    CRTP & operator=(CRTP const &) = default;
    CRTP(CRTP &&) = default;
    CRTP & operator=(CRTP &&) = default;

    auto const & asDerived() const noexcept { return static_cast<Derived const &>(*this); }
    auto & asDerived() noexcept { return static_cast<Derived &>(*this); }
    auto asDerivedPtr() const noexcept { return static_cast<Derived const *>(this); }
    auto asDerivedPtr() noexcept { return static_cast<Derived *>(this); }
};
} // namespace opensmt

#endif // OPENSMT_CRTP_H
