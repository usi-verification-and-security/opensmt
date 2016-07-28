//
// Created by Matteo Marescotti on 02/12/15.
//

#include "ClauseServer.h"
#include "lib/Log.h"


void ClauseServer::handle_accept(Socket &client) {
    Log::log(Log::INFO, "+ " + client.get_remote().toString());
}

void ClauseServer::handle_close(Socket &client) {
    Log::log(Log::INFO, "- " + client.get_remote().toString());
}

void ClauseServer::handle_exception(Socket &client, SocketException &ex) {
    Log::log(Log::WARNING, "Exception from: " + client.get_remote().toString() + ": " + ex.what());
}

void ClauseServer::handle_message(Socket &client,
                                      std::map<std::string, std::string> &header,
                                      std::string &payload) {
    Log::log(Log::INFO, "message from: " + client.get_remote().toString() + ": " + payload);
}
