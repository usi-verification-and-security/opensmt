//
// Created by prova on 13.08.19.
//

#ifndef OPENSMT_LASCORE_H
#define OPENSMT_LASCORE_H

#include <SolverTypes.h>
#include <SMTConfig.h>
#include <limits>
#include <string>

class LookaheadSMTSolver;

template<class EV>
class LABestLitBuf {
private:
    int size;
    struct EVLitPair { EV first; Lit second; };
    vec<EVLitPair> buf;
    const vec<lbool> &assigns;
    EV  heur_worst;     // the lowest heuristic value currently in buf
    int heur_worst_loc; // The location of heur_worst in buf
    inline lbool value(Lit p) const { return assigns[var(p)] ^ sign(p); }
    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed)
    {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647;
    }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size)
    {
        return (int)(drand(seed) * size);
    }

    bool randomize;
    double rnd_seed;
public:
    // Use 0 for random seed to disable randomization
    LABestLitBuf(int sz, const vec<lbool> &assigns, bool randomize, double rnd_seed)
            : size(sz), assigns(assigns), randomize(randomize), rnd_seed(rnd_seed)
    {
        for (int i = 0; i < size; i++)
            buf.push(EVLitPair{EV(), lit_Undef});
        heur_worst_loc = 0;
        heur_worst = buf[heur_worst_loc].first;
    }

    void insert(Lit l, EV &val) {
        int i;
        if (val < heur_worst) { return; }
        buf[heur_worst_loc] = EVLitPair{val, l};
        EV current_worst = EV::max_val;
        for (i = 0; i < size; i++) {
            int loc = (heur_worst_loc+i) % size;
            EV &buf_val = buf[loc].first;
            if (buf_val <= current_worst) {
                current_worst = heur_worst = buf_val;
                heur_worst_loc = loc;
            }
        }
    }

    Lit getLit(int i) {
        assert(i < size);
        assert(i >= 0);
        for (int j = 0; j < size; j++) {
            if (i + j < size && buf[i + j].second != lit_Undef && value(buf[i + j].second) == l_Undef)
                return buf[i + j].second;
            if (i - j >= 0 && buf[i - j].second != lit_Undef && value(buf[i - j].second) == l_Undef)
                return buf[i - j].second;
        }
        return lit_Undef;
    }

    Lit getLit() {
        if (randomize) {
            int i = irand(rnd_seed, size);
            return getLit(i);
        } else
            return getLit(0);
    }

    int getSize() { return size; }

    // Debug
    std::string str() const {
        std::ostringstream ss;
        ss << "[ ";
        for (int i = 0; i < size; i++)
            ss << "(" << buf[i].first.str() << "," << buf[i].second.x << ") ";
        ss << "]" << endl;

        ss << "Worst is " << heur_worst.str() << " at location " << heur_worst_loc << endl;
        return ss.str();
    }
};

class LookaheadScore {
protected:

    const vec<lbool>& assigns;
    unsigned latest_round; // The numbering for arrays

    lbool value(Var x) const { return assigns[x]; }
    lbool value(Lit p) const { return assigns[var(p)] ^ sign(p); }
public:
    void updateRound() { latest_round++; }
    explicit LookaheadScore(const vec<lbool>& assigns) : assigns(assigns), latest_round(0) {}
    virtual ~LookaheadScore() = default;
    virtual void setLAValue(Var v, int p0, int p1) = 0;

    virtual double getSolverScore(const LookaheadSMTSolver *solver) = 0;
    virtual void updateSolverScore(double &ss, const LookaheadSMTSolver *solver) = 0;

    virtual void updateLABest(Var v) =  0;
    virtual void newVar() = 0;
    virtual Lit  getBest() = 0;
    virtual void setChecked(Var v) = 0;
    virtual bool isAlreadyChecked(Var v) const = 0;
    virtual bool safeToSkip(Var v, Lit cmp) const = 0; // Given that the heuristic value of cmp is known, is it safe to skip checking value of v
};

// The deep lookahead score of a variable v is defined as
// score_p(v) + score_n(v) + 1024*score_p(v)*score_n(v), where
//  - score_p(v) = \sum_{c \in F} (1/2)^nfree((sigma . v | F), c)
//  - score_n(v) = \sum_{c \in F} (1/2)^nfree((sigma . \neg v| F), c)
//  - nfree(ss, c) is
//    - the number of free variables in clause c after ss has been run
//      until unit propagation closure, if c does not contain a true literal, or
//    - 0, if c contains a true literal
class LookaheadScoreDeep : public LookaheadScore {
public:
    class DoubleVal {
        int round;
        double val;
    public:
        DoubleVal() : round(-1), val(std::numeric_limits<double>::lowest()) {}
        DoubleVal(int round, double val) : round(round), val(val) {}
        static const DoubleVal max_val;

        bool operator<  (const DoubleVal& o) const {
            if (round > o.round) return false;
            if (round < o.round) return true;
            else {
                return (val < o.val);
            }
        }
        bool operator<= (const DoubleVal& o) const {
            if (round > o.round) return false;
            if (round < o.round) return true;
            return (val <= o.val);
        }
        int getRound() const { return round; }
        void setRound(int r) { round = r; }
    };
private:
    int base_score_round;
    LABestLitBuf<DoubleVal> buf_LABests;
    vec<DoubleVal> LAexacts;
    double cached_score;
    double computeScoreFromClauses(const vec<CRef>& clauses, const LookaheadSMTSolver *solver);
    bool current(const DoubleVal &e) const { return latest_round == static_cast<unsigned int>(e.getRound()); }
public:
    explicit LookaheadScoreDeep(const vec<lbool> &assigns, const SMTConfig &c)
            : LookaheadScore(assigns), base_score_round(-1)
            , buf_LABests(c.randomize_lookahead_bufsz(), assigns, c.randomize_lookahead(), c.getRandomSeed()) {std::cerr << "; Deep score\n";}
    void setLAValue(Var v, int p0, int p1) override;

    double getSolverScore(const LookaheadSMTSolver *solver) override;
    void updateSolverScore(double &ss, const LookaheadSMTSolver *solver) override;

    void updateLABest(Var v) override;
    void newVar() override;
    Lit  getBest() override;
    void setChecked(Var v) override;
    bool isAlreadyChecked(Var v) const override;
    bool safeToSkip(Var v, Lit cmp) const override; // Given that the heuristic value of cmp is known, is it safe to skip checking value of v
};


class LookaheadScoreClassic : public LookaheadScore {
    friend LookaheadSMTSolver;
private:
    // -----------------------------------------------------------------------------------------
    // Data type for upper bound array
    //
    class UBel {
    public:
        int ub;
        int round;

        UBel() : ub(-1), round(-1) {}

        UBel(int u, int r) : ub(u), round(r) {}

        bool operator==(const UBel &o) const { return ub == o.ub && round == o.round; }

        bool operator!=(const UBel &o) const { return !(operator==(o)); }
    };
public:
    class ExVal {
    private:
        int pprops;
        int nprops;
        int round;

        int min(int a, int b) const { return a < b ? a : b; }

        int max(int a, int b) const { return a >= b ? a : b; }

    public:
        ExVal() : pprops(-1), nprops(-1), round(-1) {}

        ExVal(int p, int n, int r) : pprops(p), nprops(n), round(r) {}

        bool operator<(const ExVal &e) const {
            if (round > e.round) return false;
            if (round < e.round) return true;
            else {
                return (min(pprops, nprops) < min(e.pprops, e.nprops)) ||
                       ((min(pprops, nprops) == min(e.pprops, e.nprops)) &&
                        (max(pprops, nprops) < max(e.pprops, e.nprops)));
            }
        }
        bool operator<=(const ExVal &e) const {
            if (round > e.round) return false;
            if (round < e.round) return true;
            return (min(pprops, nprops) <= min(e.pprops, e.nprops)) ||
                   ((min(pprops, nprops) == min(e.pprops, e.nprops)) &&
                    (max(pprops, nprops) <= max(e.pprops, e.nprops)));
        }

        bool betterPolarity() const { return pprops < nprops; } // Should return false if the literal should be unsigned
        int getRound() const { return round; }

        int getEx_l() const { return min(pprops, nprops); }

        int getEx_h() const { return max(pprops, nprops); }

        void setRound(int r) { round = r; }
        static const ExVal max_val;

        std::string str() const;
    };

private:
    class UBVal {
    private:
        UBel ub_p;
        UBel ub_n;

        bool current(const ExVal &e) const { return ub_p.round == ub_n.round && ub_p.round == e.getRound(); }

    public:
        UBVal() = default;

        UBVal(const UBel &ub_pos, const UBel &ub_neg) : ub_p(ub_pos), ub_n(ub_neg) {}

        void updateUB_p(const UBel &ub) {
            if (ub_p.round < ub.round || (ub_p.round == ub.round && ub_p.ub > ub.ub))
                ub_p = ub;
        }

        void updateUB_n(const UBel &ub) {
            if (ub_n.round < ub.round || (ub_n.round == ub.round && ub_n.ub > ub.ub))
                ub_n = ub;
        }

        bool safeToSkip(const ExVal &e) const;

        const UBel &getLow() const {
            if (ub_p.round != ub_n.round) return UBel_Undef;
            else return ub_p.ub < ub_n.ub ? ub_p : ub_n;
        }

        const UBel &getHigh() const {
            if (ub_p.round != ub_n.round) return UBel_Undef;
            else return ub_p.ub < ub_n.ub ? ub_n : ub_p;
        }
    };



    void setLAExact(Var v, int p0, int p1);


    vec<UBVal> LAupperbounds;    // The current upper bounds
    vec<ExVal> LAexacts;         // The current exact values
    LABestLitBuf<ExVal> buf_LABests;
    static const UBel UBel_Undef;

public:
    explicit LookaheadScoreClassic(const vec<lbool> &assigns, const SMTConfig &c)
            : LookaheadScore(assigns), buf_LABests(c.randomize_lookahead_bufsz(), assigns, c.randomize_lookahead(), c.getRandomSeed())
              { std::cerr << "; Classic score\n"; }

    void newVar() override;

    void updateLABest(Var v) override;

    Lit getBest() override;

    void setChecked(Var v) override;

    bool isAlreadyChecked(Var v) const override;
    bool safeToSkip(Var v, Lit cmp) const override;

    void updateLAUB(Lit l, int props);                               // Check the lookahead upper bound and update it if necessary
    void setLAValue(Var v, int pprops, int nprops) override;         // Set the exact la value

    double getSolverScore(const LookaheadSMTSolver *solver) override;

    void updateSolverScore(double &ss, const LookaheadSMTSolver *solver) override;
};
#endif //OPENSMT_LASCORE_H
