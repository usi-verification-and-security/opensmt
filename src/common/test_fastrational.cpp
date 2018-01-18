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
    FastRational m1("-2147483647");
    FastRational m2("-1073741825");
    FastRational h1("3221225472");
    FastRational r1 = m1/h1;
    FastRational r2 = m2/h1;
    FastRational e5 = r1+r2;
    printf("%s + %s = %s\n", r1.get_str().c_str(), r2.get_str().c_str(), e5.get_str().c_str());

    {
        FastRational el1("1/8589934590");
        FastRational el2("1/2");
        FastRational el3("-17895697/1152921504338411520");
        FastRational el4("2147483647/1");
        FastRational el5("1/4026531840");
        FastRational el6("2147483647/1");
        FastRational res1 = el1+el2;
        FastRational res2 = res1 + el3*el4;
        FastRational res3 = res2;// + el5*el6;
        printf("%s\n", res3.get_str().c_str());
    }
    return 0;
}
