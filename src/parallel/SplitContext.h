/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_SPLITCONTEXT_H
#define PARALLEL_SPLITCONTEXT_H

#include <common/SystemQueries.h>
#include <options/SMTConfig.h>

namespace opensmt::parallel {

class SplitContext {
    SMTConfig const & config;
    SpUnit   resource_units;
    double   resource_limit;      // Time limit for the search in resource_units
    double   next_resource_limit; // The limit at which the solver needs to stop

    // splitting state vars
    SpType   split_type;
    int      solver_limit;
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

    bool splitLimitReached(uint64_t search_counter) const {
        return useTimeAsSplitLimit() ? (cpuTime() >= split_next) : (search_counter >= split_next);
    }
    void setNextSplitLimit(uint64_t search_counter, double tuneLimit) {
        auto split_baseline = (useTimeAsSplitLimit()) ? cpuTime() : static_cast<double>(search_counter);
        split_next = split_baseline + std::max(0.0, tuneLimit);
    }

    std::vector<SplitData> splits;
public:

    std::size_t getCurrentSplitCount() const { return splits.size(); }
    std::size_t getCurrentSplitAssumptionsCount(std::size_t i)  { return splits[i].getSplitAssumptions().size(); }
    bool hasSplits() const { return not splits.empty(); }
    void enterInitCycle(uint64_t search_counter) {
        split_on = false;
        setNextSplitLimit(search_counter, initTune);
    }

    void enterTuningCycle(uint64_t search_counter) {
        split_on = false;
        setNextSplitLimit(search_counter, midTune);
    }

    void enterSplittingCycle() {
        split_on = true;
    }

    bool shouldEnterSplittingCycle(uint64_t search_counter) const {
        return splitLimitReached(search_counter);
    }

    bool isInSplittingCycle() const {
        return split_on;
    }

    int solverLimit() const { return solver_limit; }

    int splitTargetNumber() const { return split_num; }
    void insertSplitData(SplitData && data) {
        splits.emplace_back(std::move(data));
    }
    std::vector<SplitData> const & getSplits() const { return splits; }

    bool preferRandom() const { return split_preference == sppref_rand; }
    bool isSplitTypeScatter() const { return split_type == spt_scatter; }
    bool isSplitTypeLookahead() const { return split_type == spt_lookahead; }
    bool isSplitTypeNone() const { return split_type == spt_none; }
    void resetSplitType() { split_type = spt_none; }
    void setSplitTypeScatter() { split_type = spt_scatter; }
    int getSplitTypeValue() const & { return split_type.t; }
    bool resourceLimitReached(uint64_t search_counter) const {
        if (resourceLimitEnabled()) {
            if (useTimeAsResourceLimit()) {
                return time(nullptr) >= next_resource_limit;
            } else {
                return search_counter >= next_resource_limit;
            }
        }
        return false;
    }

    void setNextResourceLimit(uint64_t search_counter) {
        if (resource_limit == -1) {
            return;
        }
        next_resource_limit = useTimeAsResourceLimit() ? cpuTime() + resource_limit : search_counter + resource_limit;
    }

    void reset(uint64_t search_counter) {
        assert(config.sat_split_units() == SpUnit::time or config.sat_split_units() == SpUnit::search_counter);
        assert(config.sat_resource_units() == SpUnit::time or config.sat_resource_units() == SpUnit::search_counter);
        resource_units        = config.sat_resource_units();
        resource_limit        = config.sat_resource_limit();
        setNextResourceLimit(search_counter);
        split_type       = config.sat_split_type();
        split_on         = false;
        split_num        = config.sat_split_num();
        split_units      = config.sat_split_units();
        initTune         = config.sat_split_inittune();
        midTune          = config.sat_split_midtune();
        split_next       = split_units == SpUnit::time ? initTune + cpuTime() : initTune + search_counter;
        split_preference = config.sat_split_preference();
        solver_limit     = config.sat_solver_limit();
    }

    SplitContext(const SMTConfig & config) : config(config) { reset(0); }
};

}

#endif //PARALLEL_SPLITCONTEXT_H
