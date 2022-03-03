//
// Created by prova on 31.03.21.
//

#ifndef OPENSMT_SPLITCONFIG_H
#define OPENSMT_SPLITCONFIG_H

#include "SMTConfig.h"
#include "SystemQueries.h"

class SplitConfig {
    SMTConfig const & config;
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
    bool resourceLimitEnabled() const { return resource_limit >= 0; }
    bool useTimeAsResourceLimit() const { return resource_units == spm_time; }
    bool useTimeAsSplitLimit() const { return split_units == spm_time; }
public:
    bool splitOn() const { return split_on; }
    bool preferRandom() const { return split_preference == sppref_rand; }
    bool preferTerm() const { return split_preference == sppref_tterm; }
    bool preferFormula() const { return split_preference == sppref_bterm; }
    bool isSplitTypeScatter() const { return split_type == spt_scatter; }
    bool resourceLimitReached(uint64_t decisions) const {
        if (resourceLimitEnabled()) {
            if (useTimeAsResourceLimit()) {
                return time(nullptr) >= next_resource_limit;
            } else {
                return decisions >= next_resource_limit;
            }
        }
        return false;
    }
    int splitTargetNumber() const { return split_num; }
    bool splitStarted() const { return split_start; }
    void setNextResourceLimit(uint64_t decisions) {
        if (resource_limit == -1) {
            return;
        }
        next_resource_limit = useTimeAsResourceLimit() ? cpuTime() + resource_limit : decisions + resource_limit;
    }
    void startSplit() { split_start = true; }
    void unStartSplit() { split_start = false; }
    void continueSplit() { split_on = true; }
    void updateNextSplitLimit(uint64_t decisions) {
        split_next = useTimeAsSplitLimit() ? cpuTime() + split_midtune : decisions + split_midtune;
    }
    bool splitLimitReached(uint64_t decisions) const {
        return split_units == spm_time ? (cpuTime() >= split_next) : (decisions >= split_next);
    }

    void reset(uint64_t decisions) {
        assert(split_units == spm_time or split_units == spm_decisions);
        resource_units        = config.sat_resource_units();
        resource_limit        = config.sat_resource_limit();
        setNextResourceLimit(decisions);
        split_type            = config.sat_split_type();
        split_on              = false;
        split_start           = config.sat_split_asap();
        split_num             = config.sat_split_num();
        split_units           = config.sat_split_units();
        split_inittune        = config.sat_split_inittune();
        split_midtune         = config.sat_split_midtune();
        split_next            = split_units == spm_time ? split_inittune + cpuTime() : split_inittune + decisions;
        split_preference      = config.sat_split_preference();
        unadvised_splits      = 0;
    }
    SplitConfig(const SMTConfig & config) : config(config) { reset(0); }
};


#endif //OPENSMT_SPLITCONFIG_H
