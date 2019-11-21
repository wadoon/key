example.name = Decompose Conditional
example.path = Abstract Execution/
example.file = decomposeConditional.aer

A model of Fowler's "Decompose Conditional" refactoring. Basically several "Extract Method" applications at once for a conditional statement.

Interesting is the creation of a new abstract statement for the abstract expression; those are coupled by an abstract predicate such that it is made sure they have the same effect on either their resulting evaluation or a new boolean result variable.