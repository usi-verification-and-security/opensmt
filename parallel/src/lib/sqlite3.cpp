//
// Created by Matteo on 23/08/16.
//

#include "lib/lib.h"
#include "sqlite3.h"


SQLite3::SQLite3(std::string &db_filename) {
    int rc = sqlite3_open(db_filename.c_str(), &this->db);
    if (rc)
        throw SQLiteException(std::string("can't open: ") + db_filename);
}


SQLite3::~SQLite3() {
    sqlite3_close(this->db);
}


sqlite3_stmt *SQLite3::prepare(const std::string &sql, int n) {
    sqlite3_stmt *stmt;
    if (sqlite3_prepare(
            this->db,
            sql.c_str(),
            n,
            &stmt,
            0) != SQLITE_OK) {
        throw SQLiteException("could not prepare the statement.");
    }
    return stmt;
}


void SQLite3::finalize(sqlite3_stmt *stmt) {
    if (sqlite3_finalize(stmt) != SQLITE_OK) {
        throw SQLiteException("could not finalize the statement.");
    }
}


void SQLite3::reset(sqlite3_stmt *stmt) {
    if (sqlite3_reset(stmt) != SQLITE_OK) {
        throw SQLiteException("could not reset the statement.");
    }
}


void SQLite3::clear(sqlite3_stmt *stmt) {
    if (sqlite3_clear_bindings(stmt) != SQLITE_OK) {
        throw SQLiteException("could not clear the statement.");
    }
}


void SQLite3::exec(sqlite3_stmt *stmt) {
    if (sqlite3_step(stmt) != SQLITE_DONE) {
        throw SQLiteException("could not execute the statement.");
    }
}


void SQLite3::exec(const std::string &sql, std::function<int(int, char **, char **)> callback_row) {
    char *errc;
    int rc = sqlite3_exec(
            this->db,
            sql.c_str(),
            [](void *callback, int n, char **row, char **header) -> int {
                return (*(std::function<int(int, char **, char **)> *) callback)(n, row, header);
            },
            &callback_row,
            &errc);
    if (rc != SQLITE_OK) {
        std::string err(errc);
        sqlite3_free(errc);
        throw SQLiteException(err);
    }
}


void SQLite3::exec(const std::string &sql) {
    char *errc;
    int rc = sqlite3_exec(
            this->db,
            sql.c_str(),
            nullptr,
            nullptr,
            &errc);
    if (rc != SQLITE_OK) {
        std::string err(errc);
        sqlite3_free(errc);
        throw SQLiteException(err);
    }
}
