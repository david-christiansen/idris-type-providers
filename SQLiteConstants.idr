module SQLiteConstants

-- Successful result
SQLITE_OK : Int
SQLITE_OK = 0

-- Error codes
-- SQL error or missing database
SQLITE_ERROR : Int
SQLITE_ERROR = 1

-- Internal logic error in SQLite
SQLITE_INTERNAL : Int
SQLITE_INTERNAL = 2

-- Access permission denied
SQLITE_PERM : Int
SQLITE_PERM = 3

-- Callback routine requested an abort
SQLITE_ABORT : Int
SQLITE_ABORT = 4

-- The database file is locked
SQLITE_BUSY : Int
SQLITE_BUSY = 5

-- A table in the database is locked
SQLITE_LOCKED : Int
SQLITE_LOCKED = 6

-- A malloc() failed
SQLITE_NOMEM : Int
SQLITE_NOMEM = 7

-- Attempt to write a readonly database
SQLITE_READONLY : Int
SQLITE_READONLY = 8

-- Operation terminated by sqlite3_interrupt()
SQLITE_INTERRUPT : Int
SQLITE_INTERRUPT = 9

-- Some kind of disk I/O error occurred
SQLITE_IOERR : Int
SQLITE_IOERR = 10

-- The database disk image is malformed
SQLITE_CORRUPT : Int
SQLITE_CORRUPT = 11

-- Unknown opcode in sqlite3_file_control()
SQLITE_NOTFOUND : Int
SQLITE_NOTFOUND = 12

-- Insertion failed because database is full
SQLITE_FULL : Int
SQLITE_FULL = 13

-- Unable to open the database file
SQLITE_CANTOPEN : Int
SQLITE_CANTOPEN = 14

-- Database lock protocol error
SQLITE_PROTOCOL : Int
SQLITE_PROTOCOL = 15

-- Database is empty
SQLITE_EMPTY : Int
SQLITE_EMPTY = 16

-- The database schema changed
SQLITE_SCHEMA : Int
SQLITE_SCHEMA = 17

-- String or BLOB exceeds size limit
SQLITE_TOOBIG : Int
SQLITE_TOOBIG = 18

-- Abort due to constraint violation
SQLITE_CONSTRAINT : Int
SQLITE_CONSTRAINT = 19

-- Data type mismatch
SQLITE_MISMATCH : Int
SQLITE_MISMATCH = 20

-- Library used incorrectly
SQLITE_MISUSE : Int
SQLITE_MISUSE = 21

-- Uses OS features not supported on host
SQLITE_NOLFS : Int
SQLITE_NOLFS = 22

-- Authorization denied
SQLITE_AUTH : Int
SQLITE_AUTH = 23

-- Auxiliary database format error
SQLITE_FORMAT : Int
SQLITE_FORMAT = 24

-- 2nd parameter to sqlite3_bind out of range
SQLITE_RANGE : Int
SQLITE_RANGE = 25

-- File opened that is not a database file
SQLITE_NOTADB : Int
SQLITE_NOTADB = 26

-- sqlite3_step() has another row ready
SQLITE_ROW : Int
SQLITE_ROW = 100

-- sqlite3_step() has finished executing
SQLITE_DONE : Int
SQLITE_DONE = 101
