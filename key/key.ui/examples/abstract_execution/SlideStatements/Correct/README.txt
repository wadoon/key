example.name = Slide Statements
example.path = Abstract Execution/
example.file = slideStatements.key
example.additionalFile.1 = SlideStatements.java

A model of Fowler's "Slide Statements" refactoring.

Two statements may only be swapped if one does not write to locations the other one reads; furthermore, they may not write to the same locations, since this would also change the results.

Abrupt completion is forbidden in any case, since this would generally lead to completion due to different returned values or thrown exceptions.