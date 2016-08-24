//
// Created by Matteo on 23/08/16.
//

#ifndef CLAUSE_SERVER_SQLITE3_H
#define CLAUSE_SERVER_SQLITE3_H

#include <functional>
#include <string>
#include <vector>
#include <map>
#include <sqlite3.h>
#include "Exception.h"


class SQLiteException : public Exception {
public:
    explicit SQLiteException(const char *message) : SQLiteException(std::string(message)) { }

    explicit SQLiteException(const std::string &message) : Exception("SQLiteException: " + message) { }
};


class SQLite3 {
private:
    sqlite3 *db;
public:
    SQLite3(std::string &db_filename);

    ~SQLite3();

    sqlite3_stmt *prepare(const std::string &, int _ = -1);

    void finalize(sqlite3_stmt *);

    void reset(sqlite3_stmt *);

    void clear(sqlite3_stmt *);

    void exec(sqlite3_stmt *stmt);

    void exec(const std::string &, std::function<int(int, char **, char **)>);

    void exec(const std::string &);
};

#endif //CLAUSE_SERVER_SQLITE3_H
