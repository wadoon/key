example.name = Extract Prefix from Loop
example.path = Abstract Execution/
example.file = loopExtraction.aer

A model of a refactoring extracting a prefix of a loop, such that afterward, that prefix is executed only once (and not multiple times, inside the loop). This is an example of a refactoring that can change a non-functional property of the code: The cost of execution in terms of time and/or memory.

The refactoring can be seen as an instance of Martin Fowler's "Split Loop", where afterward the first loop is removed (only the body kept).