example.name = Rollback for Single Variable
example.path = Abstract Execution/ReplaceExceptionWithTest/
example.file = replaceExceptionWithTest.key
example.additionalFile.1 = ReplaceExceptionWithTest.java

A model of Martin Fowler's "Replace Exception with Test" refactoring. When replacing a caught exception with a test, we need a "rollback" procedure, since the progran throwing the exception might already have changed the state. In this variant, the rollback is realized for a single program variable.