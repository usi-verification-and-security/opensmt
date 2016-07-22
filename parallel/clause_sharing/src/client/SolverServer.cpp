//
// Created by Matteo on 22/07/16.
//

#include "lib/Log.h"
#include "SolverServer.h"


SolverServer::SolverServer(Settings &settings, Socket &server) :
        Server(),
        settings(settings),
        server(server),
        solver(NULL) {
    this->add_socket(&server);
}

void SolverServer::log(uint8_t level, std::string message) {
    Log::log(level, "SolverServer: " + message);
}


bool SolverServer::check_header(std::map<std::string, std::string> &header) {
    return header["name"] == this->solver->get_header()["name"] && header["hash"] == this->solver->get_header()["hash"];
}


void SolverServer::handle_close(Socket &socket) {
    if (&socket == &this->server) {
        this->log(Log::INFO, "server closed the connection");
        this->stop_solver();
    }
}

void SolverServer::handle_exception(Socket &socket, SocketException &exception) {
    this->log(Log::WARNING, "exception");
}

void SolverServer::stop_solver() {
    if (this->solver != NULL) {
        this->log(Log::INFO, this->solver->toString() + " stop");
        this->solver->stop();
        this->solver->join();
        this->del_socket(this->solver->reader());
        delete this->solver;
        this->solver = NULL;
    }
}


void SolverServer::handle_message(Socket &socket, std::map<std::string, std::string> &header, std::string &payload) {
    if (socket.get_fd() == this->server.get_fd()) {
        if (header.count("command") != 1) {
            this->log(Log::WARNING, "unexpected message from server without command");
            return;
        }
        if (header["command"] == "solve") {
            if (this->solver && this->check_header(header))
                return;
            this->stop_solver();
            this->solver = new SolverProcess(this->settings, header, payload);
            this->log(Log::INFO, this->solver->toString() + " started");
            this->add_socket(this->solver->reader());
        }
        if (header["command"] == "stop" && this->solver) {
            if (this->check_header(header))
                this->stop_solver();
        }
    }
    else if (this->solver && socket.get_fd() == this->solver->reader()->get_fd()) {
        if (!this->check_header(header))
            return;
        if (header.count("status") == 1) {
            this->log(Log::INFO, this->solver->toString() + " status: " + header["status"]);
            this->server.write(header, payload);
        }
    }
}
