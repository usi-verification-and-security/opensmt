//
// Created by Matteo on 29/08/16.
//

#include "z3++.h"

int main(int argc, char **argv) {
    z3::context c;
    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");
    z3::solver s(c);

    s.add(x >= 1);
    s.add(y < x + 3);
    s.check();
    std::cout << s.check() << "\n\n";

    z3::model m = s.get_model();
    std::cout << m << "\n\n";
    // traversing the model
    for (unsigned i = 0; i < m.size(); i++) {
        z3::func_decl v = m[i];
        // this problem contains only constants
        assert(v.arity() == 0);
        std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
    }
    // we can evaluate expressions in the model.
    std::cout << "x + y + 1 = " << m.eval(x + y + 1) << "\n";

    return 0;
}