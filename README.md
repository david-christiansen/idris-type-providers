idris-type-providers
====================

This is a type provider library for Idris.

Examples thus far:

 * A simple demonstration, in Silly.idr, that asks users for their age and
   refuses to typecheck for users under 18 years old

 * A strongly typed interface to SQLite, based roughly on the SQL
   representation in "The Power of Pi" by Oury and Swierstra (ICFP 2008).

OS Support:

For now, I only test the library on GNU/Linux. With minor changes, it should
work on other systems - primarily the build system will need updating.


To use:

First, you must build the wrapper library for SQLite.  Run "make".

Then, load Main.idr in Idris. This contains a statically-checked query.
