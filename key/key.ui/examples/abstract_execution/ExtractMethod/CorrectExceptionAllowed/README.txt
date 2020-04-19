example.name = Exceptions Allowed, but Caught
example.path = Abstract Execution/Extract Method/
example.file = extractMethodRefactoring-SurroundingTry.aer

A variant of Martin Fowler's "Extract Method" refactoring where extracted fragment may throw an exception. This exception has to be caught, however, since we want to maintain the changes to the state before. May or may not be desired. Otherwise, exceptions have to be forbidden (see other example).