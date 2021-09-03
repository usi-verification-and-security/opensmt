//
// Created by Martin Blicha on 03.09.21.
//

#ifndef OPENSMT_SPAN_H
#define OPENSMT_SPAN_H

namespace opensmt {

template<typename T>
struct Span {
    T const * pointer = nullptr;
    std::size_t length = 0;

    using iterator = T const *;

    Span() = default;

    Span(std::initializer_list<T> list) noexcept {
        length = list.size();
        pointer = list.begin();
    }

    explicit Span(vec<T> const & v) noexcept {
        length = v.size();
        pointer = v.begin();
    }

    explicit Span(std::vector<T> const & v) noexcept {
        length = v.size();
        pointer = &v[0];
    }


    std::size_t size() const { return length; }

    iterator begin() const { return pointer; }
    iterator end() const { return pointer + length; }

    T const & operator[](std::size_t i) const { return *(pointer + i); }
};

}

#endif //OPENSMT_SPAN_H
