example.name = Split Loop
example.path = Abstract Execution/
example.file = SplitLoop.aer

A model of Martin Fowler's "Split Loop" refactoring. A loop in the original program performing two jobs at once is split into two sequential loops. Uses separate abstract strongest invariants for the two parts of the loop.