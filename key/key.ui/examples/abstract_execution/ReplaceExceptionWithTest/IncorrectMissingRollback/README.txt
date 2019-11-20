example.name = Faulty - without Rollback
example.path = Abstract Execution/ReplaceExceptionWithTest/
example.file = replaceExceptionWithTest.aer

A model of Martin Fowler's "Replace Exception with Test" refactoring. When replacing a caught exception with a test, we need a "rollback" procedure, since the progran throwing the exception might already have changed the state. In this example, the rollback is missing. The proof will have corresponding open goals.