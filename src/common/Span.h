//
// Created by Martin Blicha on 03.09.21.
//

#ifndef OPENSMT_SPAN_H
#define OPENSMT_SPAN_H

namespace opensmt {

template<typename T>
struct Span {
    T * pointer = nullptr;
    std::size_t length = 0;

    using iterator = T *;
    using element_type = T;

    Span() = default;

    template<typename U,
        std::enable_if_t<std::is_const<element_type>::value and std::is_convertible_v<U,T>,
            int> = 0>
    Span(Span<U> other) noexcept {
        length = other.length;
        pointer = other.pointer;
    }

    template<typename U,
        std::enable_if_t<std::is_const<element_type>::value and std::is_convertible_v<U,T>,
            int> = 0>
    Span(std::initializer_list<U> list) noexcept {
        length = list.size();
        pointer = list.begin();
    }

    template<typename U,
        std::enable_if_t<std::is_const<element_type>::value and std::is_convertible_v<U,T>,
            int> = 0>
    explicit Span(vec<U> const & v) noexcept {
        length = v.size();
        pointer = v.begin();
    }

    explicit Span(vec<T> & v) noexcept {
        length = v.size();
        pointer = v.begin();
    }

    template<typename U,
    std::enable_if_t<std::is_const<element_type>::value and std::is_convertible_v<U,T>,
        int> = 0>
    explicit Span(std::vector<U> const & v) noexcept {
        length = v.size();
        pointer = v.data();
    }

    explicit Span(std::vector<T> & v) noexcept {
        length = v.size();
        pointer = v.data();
    }


    std::size_t size() const { return length; }

    iterator begin() const { return pointer; }
    iterator end() const { return pointer + length; }

    T const & operator[](std::size_t i) const { return *(pointer + i); }
};

template<typename T>
inline Span<const T> make_span(vec<T> const & v) { return Span<const T>(v); }

template<typename T>
inline Span<T> make_span(vec<T> & v) { return Span<T>(v); }

template<typename T>
inline Span<const T> make_span(std::vector<T> const & v) { return Span<const T>(v); }

template<typename T>
inline Span<T> make_span(std::vector<T> & v) { return Span<T>(v); }

}

#endif //OPENSMT_SPAN_H
