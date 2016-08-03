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
        record += std::to_string(std::time(NULL));
        record += "\t";
        switch (level) {
            case INFO:
                record += "INFO\t";
                break;
            case WARNING:
                system("tput setaf 3");
                record += "WARNING\t";
                break;
            case ERROR:
                system("tput setaf 9");
                record += "ERROR\t";
                break;
            default:
                record += "UNKNOWN\t";
        }
        record += message;
        mtx.lock();
        std::cout << record << "\n";
        system("tput sgr0");
        mtx.unlock();
    }

    static const uint8_t INFO = 1;
    static const uint8_t WARNING = 2;
    static const uint8_t ERROR = 3;
};


#endif //CLAUSE_SHARING_LOG_H
