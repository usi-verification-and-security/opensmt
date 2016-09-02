//
// Created by Matteo on 19/07/16.
//

#ifndef CLAUSE_SHARING_LOG_H
#define CLAUSE_SHARING_LOG_H

#include <ctime>
#include <iostream>
#include <mutex>


class Log {
private:
    Log() { }

public:
    static void log(uint8_t level, std::string message) {
        static std::mutex mtx;
        std::string record;
        record += std::to_string(std::time(nullptr));
        record += "\t";
        switch (level) {
            case INFO:
                record += "INFO\t";
                break;
            case WARNING:
                if (getenv("TERM")) {
                    system("tput setaf 3");
                    system("tput bold");
                }
                record += "WARNING\t";
                break;
            case ERROR:
                if (getenv("TERM")) {
                    system("tput setaf 9");
                    system("tput bold");
                }
                record += "ERROR\t";
                break;
            default:
                record += "UNKNOWN\t";
        }
        record += message;
        mtx.lock();
        std::cout << record << "\n";
        if (getenv("TERM"))
            system("tput sgr0");
        mtx.unlock();
    }

    static const uint8_t INFO = 1;
    static const uint8_t WARNING = 2;
    static const uint8_t ERROR = 3;
};


#endif //CLAUSE_SHARING_LOG_H
