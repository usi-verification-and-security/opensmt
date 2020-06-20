#include "Pterm.h"

    // MB: TODO this calls method that is not implemented
    void PtermAllocator::reloc(PTRef& tr, PtermAllocator& to)
    {
        Pterm& t = operator[](tr);

        if (t.reloced()) { tr = t.relocation(); return; }

        // TODO: this is not implemented!
        tr = to.alloc(t, false);
        t.relocate(tr);

        // Copy extra data-fields:
        to[tr].type(t.type());
//        if (to[tr].learnt())         to[tr].activity() = t.activity();
//        else if (to[tr].has_extra()) to[tr].calcAbstraction();
    }
