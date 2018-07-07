#include "LARefs.h"



bool BoundT::operator== (const BoundT& o) const { return o.t == t; }
BoundT BoundT::operator~ () const { return { (char)(1-t) }; }


uint32_t LVRefHash::operator() (const LVRef& s) const {return (uint32_t)s.x/8; }


void PolyRef::operator= (uint32_t v) { x = v; }


uint32_t PolyRefHash::operator() (const PolyRef& s) const {return (uint32_t)s.x;}


void PolyTermRef::operator= (uint32_t v) { x = v; }


void OccListRef::operator= (uint32_t v) { x = v; }


void OccRef::operator= (uint32_t v) { x = v; }
void LABoundRef::operator= (uint32_t v) { x = v; }
void LVRef::operator= (uint32_t v) { x = v; }
