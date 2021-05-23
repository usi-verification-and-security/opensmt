//
// Created by prova on 31.03.21.
//

#ifndef OPENSMT_SPLITCONFIG_H
#define OPENSMT_SPLITCONFIG_H

#include "SMTConfig.h"

class SplitConfig {
public:
    SpUnit   resource_units;
    double   resource_limit;      // Time limit for the search in resource_units
    double   next_resource_limit; // The limit at which the solver needs to stop

    // splitting state vars
    SpType   split_type;

    bool     split_on;
    bool     split_start;
    int      split_num;
    SpUnit   split_units;

    double   split_inittune;                                                           // Initial tuning in units.
    double   split_midtune;                                                            // mid-tuning in units.
    double   split_next;                                                               // When the next split will happen?

    SpPref   split_preference;

    int      unadvised_splits; // How many times the split happened on a PTRef that the logic considers ill-advised
    SplitConfig(const SMTConfig & config)
        : resource_units        (config.sat_resource_units())
        , resource_limit        (config.sat_resource_limit())
        , next_resource_limit   (-1)
        , split_type            (config.sat_split_type())
        , split_on              (false)
        , split_start           (config.sat_split_asap())
        , split_num             (config.sat_split_num())
        , split_units           (config.sat_split_units())
        , split_inittune        (config.sat_split_inittune())
        , split_midtune         (config.sat_split_midtune())
        , split_preference      (sppref_undef)
        , unadvised_splits      (0)
    {}
};


#endif //OPENSMT_SPLITCONFIG_H
