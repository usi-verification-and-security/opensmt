//
// Created by Matteo on 20/07/16.
//

#include "main.h"

void ClauseSharingThread::ClauseSharingServer::handle_message(Socket &socket,
                                                              std::map<std::string, std::string> &header,
                                                              std::string &payload) {


}


ClauseSharingThread::ClauseSharingThread(Settings &settings) :
        Thread(), settings(settings), server(NULL) {
    this->start();
}

ClauseSharingThread::~ClauseSharingThread() {
    delete (this->server);
}

void ClauseSharingThread::main() {
    this->server = new ClauseSharingServer(*this->reader());
    Socket clause_sharing(this->settings.clause_sharing);
    this->server->add_socket(clause_sharing);
    this->server->run_forever();
}


