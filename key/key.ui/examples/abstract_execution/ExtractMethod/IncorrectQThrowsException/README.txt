example.name = No Exceptions
example.path = Abstract Execution/Extract Method/
example.file = extractMethodRefactoring.aer

A variant of Martin Fowler's "Extract Method" refactoring where extracted fragment may not throw an exception. Allowing exceptions is possible, but one has to take into account that before the exception, local variables might have changed, which does not happen after extraction to a method. See other example for a solution around this.