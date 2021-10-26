#include "mpqpool.h"

mpq_ptr mpqPool::alloc()
{
    mpq_ptr r;
    if (!pool.empty()){
        r = pool.top();
        pool.pop();
    }
    else{
        r = store.emplace().get_mpq_t();
    }
    return r;
}

void mpqPool::release(mpq_ptr ptr)
{
    pool.push(ptr);
}
