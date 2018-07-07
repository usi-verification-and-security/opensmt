#include "PTRef.h"


uint32_t PTRefHash::operator () (const PTRef& s) const {  return (uint32_t)s.x; }
