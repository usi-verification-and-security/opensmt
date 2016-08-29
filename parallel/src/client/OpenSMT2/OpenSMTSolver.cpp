//
// Created by Matteo on 22/07/16.
//

#include "lib/lib.h"
#include "OpenSMTSolver.h"


void OpenSMTInterpret::new_solver() {
    this->solver = new OpenSMTSolver(*this);
}


OpenSMTSolver::OpenSMTSolver(OpenSMTInterpret &interpret) :
        SimpSMTSolver(interpret.config, *interpret.thandler),
        interpret(interpret),
        trail_sent(0) { }

OpenSMTSolver::~OpenSMTSolver() { }

//void _SMTSolver::clausesPublish() {
//    if (this->cls_pub == NULL)
//        return;
//    std::string s;
//    uint32_t clauses_sent = 0;
//    for (int i = 0; i < this->learnts.size(); i++) {
//        Clause &c = *this->learnts[i];
//        if (c.mark() != 3) {
//            clauses_sent++;
//            clauseSerialize(c, s);
//            c.mark(3);
//        }
//    }
//    int trail_max = this->trail_lim.size() == 0 ? this->trail.size() : this->trail_lim[0];
//    for (int i = this->trail_sent; i < trail_max; i++) {
//        clauses_sent++;
//        this->trail_sent++;
//        vec<Lit> unary;
//        unary.push(this->trail[i]);
//        clauseSerialize(unary, s);
//    }
//    if (s.length() == 0)
//        return;
//    Message m;
//
//    struct sockaddr_in sin;
//    int addrlen = sizeof(sin);
//    getsockname(this->cls_pub->fd, (struct sockaddr *) &sin, (socklen_t *) &addrlen);
//    m.header["from"].append(inet_ntoa(sin.sin_addr));
//    m.header["from"].append(":");
//    m.header["from"].append(std::to_string(sin.sin_port));
//
//    m.payload = s;
//    std::string d;
//    m.dump(d);
//
//    redisReply *reply = (redisReply *) redisCommand(this->cls_pub, "PUBLISH lemmas.%s %b",
//                                                    this->channel.c_str(),
//                                                    d.c_str(),
//                                                    d.length());
//    if (reply == NULL || reply->type == REDIS_REPLY_ERROR) {
//        std::cerr << "error during clause publishing\n";
//        if (reply != NULL)
//            freeReplyObject(reply);
////        redisFree(this->cls_pub);
////        this->cls_pub = NULL;
//        return;
//    }
//    if (reply->integer == 0)
//        std::cerr << "NO subscriber!\n";
//    freeReplyObject(reply);
//    std::cerr << "published\t" << clauses_sent << "\tclauses\n";
//    /* non block
//    redisCommand(this->c_cls_pub, "PUBLISH %s.out %b", this->channel, d.c_str(), d.length());
//    this->flush(this->c_cls_pub);
//    if (this->c_cls_pub->err != 0)
//        cerr << "Redis publish connection lost\n"; */
//}
//
//void _SMTSolver::clausesUpdate() {
//    if (this->cls_sub == NULL)
//        return;
//    /* non block
//    redisReply *reply;
//    redisBufferRead(this->c_cls_sub);
//    if (redisGetReplyFromReader(this->c_cls_sub, (void **) &reply) != REDIS_OK)
//        cerr << "Redis subscribe connection lost\n";
//    if (reply == NULL)
//        return;
//    assert (reply->type == REDIS_REPLY_ARRAY && reply->elements == 3);
//    assert (std::string(reply->element[0]->str).compare("message") == 0);
//    std::string s = std::string(reply->element[2]->str, reply->element[2]->len); */
////ZREVRANGEBYSCORE %s +inf 0 LIMIT 0 10000
//    redisReply *reply = (redisReply *) redisCommand(this->cls_sub, "SRANDMEMBER lemmas.%s 10000",
//                                                    this->channel.c_str());
//    if (reply == NULL || reply->type == REDIS_REPLY_ERROR) {
//        std::cerr << "error during clause updating\n";
//        if (reply != NULL)
//            freeReplyObject(reply);
////        redisFree(this->cls_pub);
////        this->cls_pub = NULL;
//        return;
//    }
//    if (reply->type != REDIS_REPLY_ARRAY) {
//        freeReplyObject(reply);
//        return;
//    }
//
//    for (int i = this->n_clauses; i < this->lemmas.size(); i++) {
//        if (i < this->n_clauses + reply->elements)
//            this->removeClause(*this->lemmas[i]);
//        if (i + reply->elements < this->lemmas.size())
//            this->lemmas[i] = this->lemmas[i + reply->elements];
//    }
//    this->lemmas.shrink(std::min(this->lemmas.size() - this->n_clauses, (uint32_t) reply->elements));
//
//
//    for (int i = 0; i < reply->elements; i++) {
//        std::string str = std::string(reply->element[i]->str, reply->element[i]->len);
//        vec<Lit> lits;
//        uint32_t o = 0;
//        clauseDeserialize(str, &o, lits);
//        bool f = false;
//        for (int j = 0; j < lits.size(); j++) {
//            if (!this->var_seen[var(lits[j])]) {
//                f = true;
//                break;
//            }
//        }
//        if (!f)
//            this->addClause(lits, true);
//    }
//
//    std::cerr << "updated\t\t" << reply->elements << "\tclauses\n";
///*
//    if (reply->type != REDIS_REPLY_STRING)
//        return;
//    std::string s = std::string(reply->str, reply->len);
//    Message m;
//    m.load(s);
//    //if (m.header.find("from") != m.header.end()) if (m.header["from"].compare(...) == 0)
//    //  return;
//    uint32_t o = 0;
//    while (o < m.payload.length()) {
//        vec<Lit> lits;
//        clauseDeserialize(m.payload, &o, lits);
//        solver.addClause(lits, true);
//    }
//*/
//    freeReplyObject(reply);
//}
//
//OpenSMTSolver::OpenSMTSolver(std::map<std::string, std::string>& header, SMTConfig & config, THandler & handler){
void inline OpenSMTSolver::clausesPublish() {
    if (this->interpret.clause_socket == NULL)
        return;

    std::map<std::string, std::string> header;
    std::string payload;

    uint32_t n = 0;
    int trail_max = this->trail_lim.size() == 0 ? this->trail.size() : this->trail_lim[0];
    for (int i = this->trail_sent; i < trail_max; i++) {
        this->trail_sent++;
        n++;
        PTRef pt = this->interpret.thandler->varToTerm(var(this->trail[i]));
        pt = sign(this->trail[i]) ? this->interpret.logic->mkNot(pt) : pt;
        char *s = this->interpret.thandler->getLogic().printTerm(pt, false, true);
        payload += s;
        payload += "\n";
        free(s);
    }
    if (n == 0)
        return;

    header["name"] = this->interpret.header["name"];
    header["node"] = this->interpret.header["node"];
    header["separator"] = "\n";
    header["lemmas"] = this->interpret.header["lemmas"];

    try {
        this->interpret.clause_socket->write(header, payload);
    } catch (SocketException) {
        this->interpret.clause_socket = NULL;
    }

}

void inline OpenSMTSolver::clausesUpdate() {
    if (this->interpret.clause_socket == NULL)
        return;

    std::map<std::string, std::string> header;
    std::string payload;

    header["lemmas"] = this->interpret.header["lemmas"];
    header["name"] = this->interpret.header["name"];
    header["node"] = this->interpret.header["node"];
    header["exclude"] = this->interpret.clause_socket->get_local().toString();

    try {
        Socket clauses(this->interpret.clause_socket->get_remote().toString());
        clauses.write(header, "");
        clauses.read(header, payload);
    } catch (SocketException) {
        this->interpret.clause_socket = NULL;
        return;
    }

    if (header["name"] != this->interpret.header["name"]
        || header["node"] != this->interpret.header["node"]
        || header.count("separator") == 0)
        return;

    //this->interpret.main_solver->push();

    split(payload, header["separator"], [this](std::string &lemma) {
        if (lemma.size() == 0)
            return;
        lemma = "(assert " + lemma + ")";
        this->interpret.interpFile((char *) lemma.c_str());
    });
    this->interpret.main_solver->simplifyFormulas();
}
