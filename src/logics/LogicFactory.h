//
// Created by Martin Blicha on 27.07.20.
//

#ifndef OPENSMT_LOGICFACTORY_H
#define OPENSMT_LOGICFACTORY_H

#include <string>
#include <unordered_map>

class Logic;
class ArithLogic;

namespace opensmt {

enum class Arithmetic_t : int {
    None, Difference, Linear, Nonlinear
};

struct ArithProperty {
    bool const hasInts;
    bool const hasReals;
    Arithmetic_t const arithType;
};

constexpr ArithProperty no_arith = ArithProperty{false, false, Arithmetic_t::None};

struct UFProperty {
    bool const hasArrays;
    bool const hasUF;
    bool hasDiff;
};

constexpr UFProperty no_uf = UFProperty{false, false, false};

struct BVProperty {
    bool const hasBV;
};

constexpr BVProperty no_bv = BVProperty{false};

struct LogicProperty {
    std::string const name;
    ArithProperty const arithProperty;
    UFProperty const ufProperty;
    BVProperty const bvProperty;
};

enum class Logic_t : int {
    UNDEF, EMPTY, QF_UF, QF_CUF, QF_BV, QF_RDL, QF_IDL, QF_LRA, QF_LIA, QF_NIA, QF_NRA, QF_LIRA, QF_NIRA, QF_UFRDL, QF_UFIDL,
    QF_UFLRA, QF_UFLIA, QF_UFBV, QF_AX, QF_AXDIFF, QF_BOOL, QF_AUFBV, QF_CT
};

inline const std::unordered_map<Logic_t, LogicProperty> QFLogicToProperties  {
    {Logic_t::UNDEF, {"undef",
                      no_arith,
                      no_uf,
                      no_bv}},
    {Logic_t::EMPTY, {"empty",
                      no_arith,
                      no_uf,
                      no_bv}},
    {Logic_t::QF_UF, {"QF_UF",
                      no_arith,
                      UFProperty{false, true, false},
                      no_bv}},
    {Logic_t::QF_CUF, {"QF_CUF",
                       no_arith,
                       UFProperty{false, true, false},
                       BVProperty{true}}},
    {Logic_t::QF_BV, {"QF_BV",
                      no_arith,
                      no_uf,
                      BVProperty{true}}},
    {Logic_t::QF_RDL, {"QF_RDL",
                       ArithProperty{false, true, Arithmetic_t::Difference},
                       no_uf,
                       no_bv}},
    {Logic_t::QF_IDL, {"QF_IDL",
                       ArithProperty{true, false, Arithmetic_t::Difference},
                       no_uf,
                       no_bv}},
    {Logic_t::QF_LRA, {"QF_LRA",
                       ArithProperty{false, true, Arithmetic_t::Linear},
                       no_uf,
                       no_bv}},
    {Logic_t::QF_LIA, {"QF_LIA",
                       ArithProperty{true, false, Arithmetic_t::Linear},
                       no_uf,
                       no_bv}},
    {Logic_t::QF_NIA, {"QF_NIA",
                       ArithProperty{true, false, Arithmetic_t::Nonlinear},
                       no_uf,
                       no_bv}},
    {Logic_t::QF_NRA, {"QF_NRA",
                       ArithProperty{false, true, Arithmetic_t::Nonlinear},
                       no_uf,
                       no_bv}},
    {Logic_t::QF_LIRA, {"QF_LIRA",
                        ArithProperty{true, true, Arithmetic_t::Linear},
                        no_uf,
                        no_bv}},
    {Logic_t::QF_NIRA, {"QF_NIRA",
                        ArithProperty{true, true, Arithmetic_t::Nonlinear},
                        no_uf,
                        no_bv}},
    {Logic_t::QF_UFRDL, {"QF_UFRDL",
                         ArithProperty{false, true, Arithmetic_t::Difference},
                         UFProperty{true, false, false},
                         no_bv}},
    {Logic_t::QF_UFIDL, {"QF_UFIDL",
                         ArithProperty{true, false, Arithmetic_t::Difference},
                         UFProperty{true, false, false},
                         no_bv}},
    {Logic_t::QF_UFLRA, {"QF_UFLRA",
                         ArithProperty{false, true, Arithmetic_t::Linear},
                         UFProperty{true, false, false},
                         no_bv}},
    {Logic_t::QF_UFLIA, {"QF_UFLIA",
                         ArithProperty{true, false, Arithmetic_t::Linear},
                         UFProperty{true, false, false},
                         no_bv}},
    {Logic_t::QF_UFBV, {"QF_UFBV",
                        no_arith,
                        UFProperty{false, true, false},
                        no_bv}},
    {Logic_t::QF_AX, {"QF_AX",
                      no_arith,
                      UFProperty{true, false},
                      no_bv}},
    {Logic_t::QF_AXDIFF, {"QF_AXDIFF",
                      no_arith,
                      UFProperty{true, false, true},
                      no_bv}},
    {Logic_t::QF_BOOL, {"QF_BOOL",
                        no_arith,
                        no_uf,
                        no_bv}},
    {Logic_t::QF_AUFBV, {"QF_AUFBV",
                          no_arith,
                          UFProperty{true, true, false},
                          BVProperty{true}}},
     {Logic_t::QF_CT, {"QF_CT",
                        no_arith,
                        no_uf,
                        no_bv}}
};

Logic_t getLogicFromString(const std::string & name);

std::string getStringFromLogic(const Logic_t logic);


class LogicFactory {
public:
    static Logic * getInstance(Logic_t);
    static ArithLogic * getLRAInstance();
    static ArithLogic * getLIAInstance();
};
}
#endif //OPENSMT_LOGICFACTORY_H
