/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_SPLITCONTEXT_H
#define OPENSMT_SPLITCONTEXT_H

#include "SMTConfig.h"
#include "SystemQueries.h"

class SplitContext {
    SMTConfig const & config;
    SpUnit   resource_units;
    double   resource_limit;      // Time limit for the search in resource_units
    double   next_resource_limit; // The limit at which the solver needs to stop

    // splitting state vars
    SpType   split_type;

    bool     split_on;
    int      split_num;
    SpUnit   split_units;

    double   initTune; // Initial tuning in units.
    double   midTune; // mid-tuning in units.
    double   split_next; // When the next split will happen?

    SpPref   split_preference;

    bool resourceLimitEnabled() const { return resource_limit >= 0; }
    bool useTimeAsResourceLimit() const { return resource_units == SpUnit::time; }
    bool useTimeAsSplitLimit() const { return split_units == SpUnit::time; }

    bool splitLimitReached(uint64_t decisions) const {
        return useTimeAsSplitLimit() ? (cpuTime() >= split_next) : (decisions >= split_next);
    }
    void setNextSplitLimit(uint64_t decisions, double tuneLimit) {
        auto split_baseline = (useTimeAsSplitLimit()) ? cpuTime() : static_cast<double>(decisions);
        split_next = split_baseline + std::max(0.0, tuneLimit);
    }

    std::vector<SplitData> splits;
public:

    int getCurrentSplitCount() const { return splits.size(); }
    bool hasCurrentSplits() const { return not splits.empty(); }
    void enterInitCycle(uint64_t decisions) {
        split_on = false;
        setNextSplitLimit(decisions, initTune);
    }

    void enterTuningCycle(uint64_t decisions) {
        split_on = false;
        setNextSplitLimit(decisions, midTune);
    }

    void enterSplittingCycle() {
        split_on = true;
    }

    bool shouldEnterSplittingCycle(uint64_t decisions) const {
        return splitLimitReached(decisions);
    }

    bool isInSplittingCycle() const {
        return split_on;
    }

    int splitTargetNumber() const { return split_num; }
    void insertSplitData(SplitData && data) {
        splits.emplace_back(std::move(data));
    }
    std::vector<SplitData> const & getSplits() const { return splits; }

    bool preferRandom() const { return split_preference == sppref_rand; }
    bool preferTerm() const { return split_preference == sppref_tterm; }
    bool preferFormula() const { return split_preference == sppref_bterm; }
    bool preferNotEq() const { return split_preference == sppref_noteq; }
    bool preferEq() const { return split_preference == sppref_eq; }
    bool preferTermNotEq() const { return split_preference == sppref_tterm_neq; }
    bool isSplitTypeScatter() const { return split_type == spt_scatter; }
    bool isSplitTypeLookahead() const { return split_type == spt_lookahead; }
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

    void setNextResourceLimit(uint64_t decisions) {
        if (resource_limit == -1) {
            return;
        }
        next_resource_limit = useTimeAsResourceLimit() ? cpuTime() + resource_limit : decisions + resource_limit;
    }

    void reset(uint64_t decisions) {
        assert(config.sat_split_units() == SpUnit::time or config.sat_split_units() == SpUnit::decisions);
        assert(config.sat_resource_units() == SpUnit::time or config.sat_resource_units() == SpUnit::decisions);
        resource_units        = config.sat_resource_units();
        resource_limit        = config.sat_resource_limit();
        setNextResourceLimit(decisions);
        split_type       = config.sat_split_type();
        split_on         = false;
        split_num        = config.sat_split_num();
        split_units      = config.sat_split_units();
        initTune         = config.sat_split_inittune();
        midTune          = config.sat_split_midtune();
        split_next       = split_units == SpUnit::time ? initTune + cpuTime() : initTune + decisions;
        split_preference = config.sat_split_preference();
    }

    SplitContext(const SMTConfig & config, uint64_t decisions) : config(config) { reset(decisions); }
};


#endif //OPENSMT_SPLITCONTEXT_H
