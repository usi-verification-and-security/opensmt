#include "Sort.h"

//const SRef SRef_Undef = -1;

/***********************************************************
 * Identifier constructor
 ***********************************************************/
Identifier::Identifier(ASTNode& n) {
    name = string(n.getValue());
    if (n.children == NULL) type = IDTYPE_SIMPLE;
    else {
        type = IDTYPE_CMPLX;
        for (list<ASTNode*>::iterator it = n.children->begin(); it != n.children->end(); it++)
            numlist.push(atoi((**it).getValue()));
    }
}

sortid_t Sort::static_uniq_id = 0;

//=============================================================================
// Sort constructor
//

Sort::Sort(ASTNode& sn)
{
    uniq_id = static_uniq_id++;
    stringstream ss;
    if (sn.getType() == CMD_T) {
        list<ASTNode*>::iterator p = sn.children->begin();
        ASTNode& sym_name = **p; p++;
        ASTNode& num      = **p;
        id = new Identifier(sym_name);
        par_num = atoi(num.getValue());
        stype = SORT_ID_SIMPL;
        ss << sym_name.getValue();
        ss << " " << par_num;
        canon_name = strdup(ss.str().c_str());
    }
    else if (sn.getType() == ID_T) {
        id = new Identifier(**(sn.children->begin()));
        stype = SORT_ID_SIMPL;
        ss << id->toString();
        ss << " " << 0;
        canon_name = strdup(ss.str().c_str());
    }
    else if (sn.getType() == LID_T) {
        type = S_ID_LIST;
        list<ASTNode*>::iterator it = sn.children->begin();
        id = new Identifier(**(it++));
        for (; it != sn.children->end(); it++)
            rest_sorts.push(new Sort(**it));
        // Check this from the logic?
        stype = SORT_ID_CMPLX;
        canon_name = strdup(ss.str().c_str());
    }
    else assert(false);
}

Sort::Sort(Identifier& id, vec<Sort*>& rest) : id(&id)
{
    uniq_id = static_uniq_id++;
    if (rest.size() == 0)
        stype = SORT_ID_SIMPL;
    else {
        for (int i = 0; i < rest.size(); i++)
            rest_sorts.push(rest[i]);
        stype = SORT_ID_CMPLX;
    }
    stringstream ss;
    ss << id.toString();
    if (type != S_ID) {
        ss << " ( ";
        for (int i = 0; i < rest_sorts.size(); i++)
            ss << (*(rest_sorts[i])).getCanonName() << " ";
        ss << ") ";
    }
    canon_name = strdup(ss.str().c_str());
};

Sort::Sort(Identifier& id) : id(&id)
{
    stringstream ss;
    ss << id.toString();
    if (id.getType() == IDTYPE_SIMPLE) ss << " 0";
    canon_name = strdup(ss.str().c_str());
    uniq_id = static_uniq_id++;
};


bool hasSortBool() {
    return true;
}
