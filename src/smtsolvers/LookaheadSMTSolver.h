//
// Created by prova on 07.02.19.
//

#ifndef OPENSMT_LOOKAHEADSMTSOLVER_H
#define OPENSMT_LOOKAHEADSMTSOLVER_H

#include "SimpSMTSolver.h"

class LookaheadSMTSolver : public SimpSMTSolver {

    uint32_t latest_round;                      // The numbering for arrays
    void updateRound() { latest_round++; }
    // -----------------------------------------------------------------------------------------
    // Data type for exact value array
    static inline int min(int i, int j) { return i < j ? i : j; }
    static inline int max(int i, int j) { return i > j ? i : j; }

    class ExVal
    {
    private:
        int pprops;
        int nprops;
        int round;
    public:
        ExVal() : pprops(-1), nprops(-1), round(-1) {}
        ExVal(int p, int n, int r) : pprops(p), nprops(n), round(r) {}
        bool operator< (const ExVal& e) const
        {
            return (round < e.round) ||
                   (min(pprops, nprops) < min(e.pprops, e.nprops)) ||
                   ((min(pprops, nprops) == min(e.pprops, e.nprops)) && (max(pprops, nprops) < max(e.pprops, e.nprops)));
        }
        bool betterPolarity() const { return pprops < nprops; } // Should return false if the literal should be unsigned
        int  getRound()       const { return round; }
        int  getEx_l()        const { return min(pprops, nprops); }
        int  getEx_h()        const { return max(pprops, nprops); }
        void setRound(int r)        { round = r; }
    };

    // -----------------------------------------------------------------------------------------
    // Data type for upper bound array
    //
    class UBel
    {
    public:
        int ub;
        int round;

        UBel() : ub(-1), round(-1) {}
        UBel(int u, int r) : ub(u), round(r) {}

        bool operator== (const UBel& o) const { return ub == o.ub && round == o.round; }
        bool operator!= (const UBel& o) const { return !(operator==(o)); }
    };

    static const UBel UBel_Undef;

    class UBVal
    {
    private:
        UBel ub_p;
        UBel ub_n;
        bool current(const ExVal& e) const { return ub_p.round == ub_n.round && ub_p.round == e.getRound(); }
    public:
        UBVal() {}
        UBVal(const UBel& ub_pos, const UBel& ub_neg) : ub_p(ub_pos), ub_n(ub_neg) {}
        void updateUB_p(const UBel& ub) { if (ub_p.round < ub.round || (ub_p.round == ub.round && ub_p.ub > ub.ub)) ub_p = ub; }
        void updateUB_n(const UBel& ub) { if (ub_n.round < ub.round || (ub_n.round == ub.round && ub_n.ub > ub.ub)) ub_n = ub; }

        bool safeToSkip(const ExVal& e) const;
        const UBel& getUB_p()  const { return ub_p; }
        const UBel& getUB_n()  const { return ub_n; }
        bool betterThan(const ExVal& e) const;
        const UBel& getLow() const
        {
            if (ub_p.round != ub_n.round) return UBel_Undef;
            else return ub_p.ub < ub_n.ub ? ub_p : ub_n;
        }
        const UBel& getHigh() const
        {
            if (ub_p.round != ub_n.round) return UBel_Undef;
            else return  ub_p.ub < ub_n.ub ? ub_n : ub_p;
        }
    };

    // The result from the lookahead loop
    enum class LALoopRes
    {
        sat,
        unsat,
        unknown,
        splits,
        restart
    };

    class laresult {
    public:
        enum result { tl_unsat, sat, restart, unsat, ok };
    private:
        result value;
    public:
        explicit laresult(result v) : value(v) {}
        bool operator == (laresult o) const { return o.value == value; }
        bool operator != (laresult o) const { return o.value != value; }
    };

    laresult la_tl_unsat;
    laresult la_sat;
    laresult la_restart;
    laresult la_unsat;
    laresult la_ok;

    LALoopRes solveLookahead(int d, int &idx, ConflQuota confl_quota);

	bool betterThan_ub(const UBVal& ub, const ExVal& e) const;

    void updateLABest(Var v);

    vec<UBVal>          LAupperbounds;    // The current upper bounds
    vec<ExVal>          LAexacts;         // The current exact values

	int la_round;                         // Keeps track of the lookahead round (used in lower bounds)
    class LABestLitBuf {
        private:
            int size;
            vec<Pair<ExVal,Lit> > buf;
            vec<lbool>& assigns;
            inline lbool value(Lit p) const { return assigns[var(p)]^sign(p); }
            bool randomize;
            double rnd_seed;
        public:
            // Use 0 for random seed to disable randomization
            LABestLitBuf(int sz, vec<lbool>& assigns, bool randomize, double rnd_seed)
                : size(sz)
                , assigns(assigns)
                , randomize(randomize)
                , rnd_seed(rnd_seed) {
                for (int i = 0; i < size; i++)
                    buf.push(Pair<ExVal,Lit>{ExVal(), lit_Undef});
            }
            void insert(Lit l, ExVal& val) {
                int i;
                for (i = 0; i < size; i++) {
                    ExVal &buf_val = buf[i].first;
                    Lit buf_l = buf[i].second;
                    if ((buf_val < val) || (value(buf_l) != l_Undef))
                        break;
                }
                if (i == size)
                    return;

                Pair<ExVal,Lit> new_next = buf[i];
                buf[i++] = Pair<ExVal,Lit>{val,l};
                for (; i < size; i++) {
                    Pair<ExVal,Lit> tmp = buf[i];
                    buf[i] = new_next;
                    new_next = tmp;
                }
            }
            Lit getLit(int i) {
                assert(i < size);
                assert(i >= 0);
                for (int j = 0; j < size; j++) {
                    if (i+j < size && buf[i+j].second != lit_Undef && value(buf[i+j].second) == l_Undef)
                        return buf[i+j].second;
                    if (i-j >= 0 && buf[i-j].second != lit_Undef && value(buf[i-j].second) == l_Undef)
                        return buf[i-j].second;
                }
                return lit_Undef;
            }
            Lit getLit() {
                if (randomize) {
                    int i = CoreSMTSolver::irand(rnd_seed, size);
                    return getLit(i);
                }
                else
                    return getLit(0);
            }
            int getSize() { return size; }
    };

    LABestLitBuf buf_LABests;


    void     updateLAUB       (Lit l, int props);                                      // Check the lookahead upper bound and update it if necessary
    laresult lookahead_loop   (Lit& best, int &idx, ConflQuota &confl_quota);
    void     setLAExact       (Var v, int pprops, int nprops);                         // Set the exact la value
    lbool    LApropagate_wrapper(ConflQuota &confl_quota);

    bool createSplit_lookahead();

protected:
    lbool solve_() override;                                                            // Does not change the formula
public:
    LookaheadSMTSolver(SMTConfig&, THandler&);
    Var newVar(bool sign, bool dvar) override;
};


#endif //OPENSMT_LOOKAHEADSMTSOLVER_H
