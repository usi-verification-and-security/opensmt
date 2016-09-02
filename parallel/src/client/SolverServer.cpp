//
// Created by Matteo on 22/07/16.
//

#include <unistd.h>
#include "lib/Log.h"
#include "SolverServer.h"


SolverServer::SolverServer(Address &server) :
        Server(),
        server(Socket(server)),
        lemmas(nullptr),
        solver(nullptr) {
    std::map<std::string, std::string> header;
    header["solver"] = SolverProcess::solver;
    this->server.write(header, "");
    this->add_socket(&this->server);
}

void SolverServer::log(uint8_t level, std::string message, std::map<std::string, std::string> *header_solver) {
//    std::map<std::string, std::string> header;
//    if (header_solver != nullptr) {
//        for(auto &pair:header_solver)
//        header["command"] = "log";
//        header["level"] = std::to_string(level);
//        try {
//            this->server.write(header, message);
//        } catch (SocketException) { }
//    }
    Log::log(level, message + (this->solver ? ": " + this->solver->header["name"] + this->solver->header["node"] : ""));
}


bool SolverServer::check_header(std::map<std::string, std::string> &header) {
    if (this->solver == nullptr)
        return false;
    return header["name"] == this->solver->header["name"] && header["node"] == this->solver->header["node"];
}


void SolverServer::handle_close(Socket &socket) {
    if (&socket == &this->server) {
        this->log(Log::INFO, "server closed the connection");
        this->stop_solver();
        if (this->lemmas != nullptr)
            delete this->lemmas;
    }
    else if (&socket == this->lemmas) {
        if (this->solver)
            this->log(Log::WARNING, "lemma server closed the connection during solving");
        else
            this->log(Log::INFO, "lemma server closed the connection");
        delete this->lemmas;
        this->lemmas = nullptr;
    }
    else if (this->solver && &socket == this->solver->reader()) {
        this->log(Log::ERROR, "solver quit unexpectedly");
        this->solver->header["error"] = "unexpected quit";
        this->server.write(this->solver->header, "");
        this->stop_solver();
    }
}

void SolverServer::handle_exception(Socket &socket, SocketException &exception) {
    this->log(Log::WARNING, exception.what());
}

void SolverServer::stop_solver() {
    if (this->solver != nullptr) {
        this->del_socket(this->solver->reader());
        this->solver->stop();
        this->solver->join();
        delete this->solver;
        this->solver = nullptr;
    }
}


void SolverServer::handle_message(Socket &socket, std::map<std::string, std::string> &header, std::string &payload) {
    if (socket.get_fd() == this->server.get_fd()) {
        if (header.count("command") != 1) {
            this->log(Log::WARNING, "unexpected message from server without command");
            return;
        }
        if (header["command"] == "lemmas" && header.count("lemmas") == 1) {
            this->log(Log::INFO, "new lemma server " + header["lemmas"]);
            if (this->lemmas != nullptr) {
                delete this->lemmas;
                this->lemmas = nullptr;
            }
            try {
                this->lemmas = new Socket(header["lemmas"]);
                this->add_socket(this->lemmas);
            }
            catch (SocketException ex) {
                this->log(Log::ERROR, "connection error to lemma server " + header["lemmas"]);
            }
        }
        else if (header["command"] == "solve") {
            if (this->check_header(header))
                return;
            this->stop_solver();
            this->solver = new SolverProcess(this->lemmas, header, payload);
            this->add_socket(this->solver->reader());
            this->log(Log::INFO, "start");
        }
        else if (header["command"] == "stop" && this->check_header(header)) {
            this->log(Log::INFO, "stop");
            this->stop_solver();
        }
    }
    else if (this->solver && socket.get_fd() == this->solver->reader()->get_fd()) {
        this->server.write(header, payload);
        this->solver->header = header;
        if (header.count("status") == 1) {
            this->log(Log::INFO, header["status"]);
        }
    }
}
