#ifndef MPQPOOL_H
#define MPQPOOL_H
#include <stack>
#include <vector>
#include <gmpxx.h>

class mpqPool
{
    std::stack<mpq_class> store; // uses deque as storage to avoid realloc
    std::stack<mpq_ptr, std::vector<mpq_ptr>> pool;
public:
    mpq_ptr alloc();
    void release(mpq_ptr);
};
#endif // MPQPOOL_H
