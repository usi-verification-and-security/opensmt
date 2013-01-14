#include "Enode.h"
#include "EnodeStore.h"
#include "Term.h"

int main(int argc, char **argv) {
    EnodeStore estore;
    ERef er = estore.addSymb(TRef_Undef);
    estore.addTerm(er);
    return 0;
}
