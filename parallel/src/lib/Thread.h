//
// Created by Matteo Marescotti on 02/12/15.
//

#ifndef CLAUSE_SHARING_THREAD_H
#define CLAUSE_SHARING_THREAD_H

#include <thread>
#include <mutex>
#include <atomic>
#include <iostream>
#include "Exception.h"
#include "net.h"


#ifdef __APPLE__

#ifdef __cplusplus
extern "C" {
#endif

#if !defined(PTHREAD_BARRIER_SERIAL_THREAD)
# define PTHREAD_BARRIER_SERIAL_THREAD  (1)
#endif

#if !defined(PTHREAD_PROCESS_PRIVATE)
# define PTHREAD_PROCESS_PRIVATE    (42)
#endif
#if !defined(PTHREAD_PROCESS_SHARED)
# define PTHREAD_PROCESS_SHARED     (43)
#endif

typedef struct {
    char c;
} pthread_barrierattr_t;

typedef struct {
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    unsigned int limit;
    unsigned int count;
    unsigned int phase;
} pthread_barrier_t;

int pthread_barrierattr_init(pthread_barrierattr_t *attr);
int pthread_barrierattr_destroy(pthread_barrierattr_t *attr);

int pthread_barrierattr_getpshared(const pthread_barrierattr_t *attr,
                                   int *pshared);
int pthread_barrierattr_setpshared(pthread_barrierattr_t *attr,
                                   int pshared);

int pthread_barrier_init(pthread_barrier_t *barrier,
                         const pthread_barrierattr_t *attr,
                         unsigned int count);
int pthread_barrier_destroy(pthread_barrier_t *barrier);

int pthread_barrier_wait(pthread_barrier_t *barrier);

#ifdef  __cplusplus
}
#endif

#endif /* __APPLE__ */


class Thread {
private:
    std::thread *thread;
    pthread_barrier_t barrier;
    Pipe piper;
    Pipe pipew;
    std::mutex mtx;
    std::atomic<bool> stop_requested;

    void thread_wrapper();

protected:
    virtual void main() = 0;

    virtual void start();

public:
    Thread();

    virtual ~Thread();

    void stop();

    void join();

    inline bool joinable();

    Socket *reader();

    Socket *writer();

};


#endif //CLAUSE_SHARING_THREAD_H
