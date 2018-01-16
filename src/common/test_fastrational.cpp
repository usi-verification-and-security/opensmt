#include "FastRational.h"

int main(int argc, char** argv)
{
    FastRational r("-2147483648");
    FastRational n("0");
    FastRational e = n-r;
    printf("%d\n", WORD_MIN);
    printf("%s - %s = %s\n", n.get_str().c_str(), r.get_str().c_str(), e.get_str().c_str());

    FastRational s = r / 5;
    FastRational e2 = s/s;
    printf("%s / %s = %s\n", s.get_str().c_str(), s.get_str().c_str(), e2.get_str().c_str());

    FastRational t("-2");
    FastRational n1("-1998");
    FastRational d1("1001");
    FastRational frac = n1/d1;
    FastRational e3 = t/frac;
    printf("%s / %s = %s\n", t.get_str().c_str(), frac.get_str().c_str(), e3.get_str().c_str());

    FastRational unit("-1");
    FastRational e4 = r/unit;
    printf("%s/%s = %s\n", r.get_str().c_str(), unit.get_str().c_str(), e4.get_str().c_str());
    return 0;
}
