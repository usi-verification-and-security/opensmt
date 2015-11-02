#include "common/Global.h"

int main(int argc, const char** argv)
{
    char* output;
    if (argc == 1) {
        printf("Usage: %s [str [str ... ] ]\n", argv[0]);
        return 1;
    }
    for (int i = 1; i < argc; i++) {
        char* rat;
        bool rval = opensmt::stringToRational(rat, argv[i]);
        if (rval == true) {
            printf("%s => %s\n", argv[i], rat);
            free(rat);
        }
        else
            printf("Error converting: %s\n", argv[i]);
    }
}
