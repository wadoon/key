example.name = Correct - with Rollback
example.path = Abstract Execution/ReplaceExceptionWithTest/
example.file = replaceExceptionWithTest.aer

A model of Martin Fowler's "Replace Exception with Test" refactoring. When replacing a caught exception with a test, we need a "rollback" procedure, since the program throwing the exception might already have changed the state. In this (working) variant, a dedicated abstract statement resets the whole possibly affected state to a safe one.