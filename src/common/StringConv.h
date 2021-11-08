/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_STRINGCONV_H
#define OPENSMT_STRINGCONV_H

#include "NumberUtils.h"

namespace opensmt {

   class strConvException : std::exception {
        char *reason;
    public:
        strConvException(const char *reason_) {
            int res = asprintf(&reason, "Error converting string to rational.  %s is not a legal rational", reason_);
            assert(res >= 0);
            (void) res;
        }

        virtual const char *what() const noexcept {
            return reason;
        }

        ~strConvException() { free(reason); }
    };

    bool static inline isDigit(char c) {
        return (c >= '0' && c <= '9');
    }

    bool static inline isPosDig(char c) {
        return (c > '0' && c <= '9');
    }

    bool static inline isIntString(char const *str) {
        if (str[0] == '\0') return false;

        bool isInt = true;
        for (int i = str[0] == '-' ? 1 : 0; str[i] != '\0'; i++) {
            if (str[i] < '0' or str[i] > '9') {
                isInt = false;
                break;
            }
        }
        return isInt;
    }

    bool static inline isRealString(char const *str) {
        if (str[0] == '\0') return false;
        enum t_State {
            S0, S1, S2, S3, S4, S5, S6, S7
        };
        auto isDigit = [](char const c) { return c >= '0' and c <= '9'; };
        t_State state = S0;
        bool unexpectedSymbol = false;
        for (int i = str[0] == '-' ? 1 : 0; str[i] != '\0' and not unexpectedSymbol; i++) {
            switch (state) {
                case S0:
                    if (str[i] == '.') state = S2;
                    else if (isDigit(str[i])) state = S1;
                    else unexpectedSymbol = true;
                    break;
                case S1:
                    if (str[i] == '.') state = S2;
                    else if (isDigit(str[i])) state = S1;
                    else if (str[i] == '/') state = S4;
                    else unexpectedSymbol = true;
                    break;
                case S2:
                    if (isDigit(str[i])) state = S3;
                    else unexpectedSymbol = true;
                    break;
                case S3:
                    if (isDigit(str[i])) state = S3;
                    else if (str[i] == '/') state = S4;
                    else unexpectedSymbol = true;
                    break;
                case S4:
                case S5:
                    if (isDigit(str[i])) state = S5;
                    else if (str[i] == '.') state = S6;
                    else unexpectedSymbol = true;
                    break;
                case S6:
                case S7:
                    if (isDigit(str[i])) state = S7;
                    else unexpectedSymbol = true;
                    break;
            }
        }
        if (unexpectedSymbol) return false;
        switch (state) {
            case S1:
            case S3:
            case S5:
            case S7:
                return true;
            case S0:
            case S2:
            case S4:
            case S6:
                return false;
        }
        assert(false); // Unreachable
        return false;
    }

    bool static inline stringToRational(char *&rat, const char *flo) {
        int nom_l = 0;
        int den_l = 1;
        int state = 0;
        int zeroes = 0;
        bool is_frac = false;
        bool is_neg = false;

        if (flo[0] == '-') {
            flo++;
            is_neg = true;
        }

        for (int i = 0; flo[i] != '\0'; i++) {
            if (state == 0 && flo[i] == '0') {}
            else if (state == 0 && isPosDig(flo[i])) {
                nom_l++;
                state = 1;
            } else if (state == 0 && flo[i] == '.') { state = 4; }
            else if (state == 0 && flo[i] == '/') {
                state = 5;
                is_frac = true;
            } else if (state == 1 && isDigit(flo[i])) {
                nom_l++;
                state = 1;
            } else if (state == 1 && flo[i] == '.') { state = 2; }
            else if (state == 1 && flo[i] == '/') {
                state = 5;
                is_frac = true;
            } else if (state == 2 && flo[i] == '0') {
                zeroes++;
                state = 3;
            } else if (state == 2 && isPosDig(flo[i])) {
                nom_l++;
                state = 2;
            } else if (state == 3 && flo[i] == '0') {
                zeroes++;
                state = 3;
            } else if (state == 3 && isPosDig(flo[i])) {
                nom_l += zeroes + 1;
                zeroes = 0;
                state = 2;
            } else if (state == 4 && flo[i] == '0') { state = 4; }
            else if (state == 4 && isPosDig(flo[i])) {
                nom_l++;
                state = 2;
            }
                // We come here if it is a fraction already
            else if (state == 5 && isDigit(flo[i])) { state = 5; }
            else { throw strConvException(flo); }
        }

        if (is_frac) {
            normalize(rat, flo, is_neg);
            return true;
        }

        if (nom_l == 0) {
            normalize(rat, "0", false);
            return true;
        }

        state = 0;
        zeroes = 0;
        for (int i = 0; flo[i] != '\0'; i++) {
            if (state == 0 && isDigit(flo[i])) { state = 0; }
            else if (state == 0 && flo[i] == '.') { state = 1; }
            else if (state == 1 && isPosDig(flo[i])) {
                state = 1;
                den_l++;
            } else if (state == 1 && flo[i] == '0') {
                state = 2;
                zeroes++;
            } else if (state == 2 && flo[i] == '0') {
                state = 2;
                zeroes++;
            } else if (state == 2 && isPosDig(flo[i])) {
                state = 1;
                den_l += zeroes + 1;
                zeroes = 0;
            }
        }

//    printf("The literal %s, once converted, will have denominator of length %d and nominator of length %d characters\n", flo, den_l, nom_l);
        char *rat_tmp = (char *) malloc(nom_l + den_l + 2);
        rat_tmp[0] = '\0';

        int i, j;
        state = -1;
        for (i = j = 0; j < nom_l; i++) {
            assert(flo[i] != '\0');
            if (state == -1 && flo[i] != '.' && flo[i] != '0') {
                rat_tmp[j++] = flo[i];
                state = 0;
            } else if (state == -1 && flo[i] == '.') {}
            else if (state == -1 && flo[i] == '0') {}
            else if (state == 0 && flo[i] != '.') { rat_tmp[j++] = flo[i]; }
            else if (state == 0 && flo[i] == '.') {}
        }
        rat_tmp[j++] = '/';
        rat_tmp[j++] = '1';
        for (i = 0; i < den_l - 1; i++) rat_tmp[j++] = '0';
        rat_tmp[j] = '\0';
        normalize(rat, rat_tmp, is_neg);
        free(rat_tmp);
        return true;
    }
}

#endif //OPENSMT_STRINGCONV_H
