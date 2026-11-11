#ifndef OPENSMT_VIEW_H
#define OPENSMT_VIEW_H

#include <ranges>

namespace opensmt {

template<typename V>
class VectorView : public std::ranges::view_interface<VectorView<V>> {
public:
    using Vector = V;
    using Iterator = typename Vector::const_iterator;

    VectorView() = default;
    VectorView(Vector const & vec) : VectorView(vec.cbegin(), vec.cend()) {}
    VectorView(Iterator begin_, Iterator end_) : _begin(begin_), _end(end_) {}

    Iterator begin() const { return _begin; }
    Iterator end() const { return _end; }

private:
    Iterator _begin{};
    Iterator _end{};
};

} // namespace opensmt

#endif // OPENSMT_VIEW_H
