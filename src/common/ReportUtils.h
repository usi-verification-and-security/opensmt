/*
 *  Copyright (c) 2008-2012, Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
 *  Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_REPORTUTILS_H
#define OPENSMT_REPORTUTILS_H

#define opensmt_warning( S )      { std::cerr << "; Warning: " << S << std::endl; }
#define opensmt_warning2( S, T )  { cerr << "; Warning: " << S << " " << T << endl; }

#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )

#endif //OPENSMT_REPORTUTILS_H
