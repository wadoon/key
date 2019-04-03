example.name = BACKGROUND
example.path = Abstract Execution

Abstract Execution is an analysis technique with which one can show properties not only for all possible inputs (like in symbolic execution), but also for all possible programs satisfying certain constraints, in other words: Properties about abstract programs. The keyword "abstract_statement P;" is used to declare an "Abstract Placeholder Statement" (APS) which can represent infinitely many programs. APSs can be augmented by JML specifications constraining their input/output and irregular termination behavior.

The examples in this section are taken from the original "Abstract Execution"paper by Dominic Steinhoefel and Reiner Haehnle, submitted to FM 2019. They model refactoring techniques as described by Martin Fowler (Fowler 1999, Fowler 2018) and proof them correct, where implicit assumptions made by Fowler have been made explicit for the proof to work.

Please always load the ".key" files associated to the examples, as loading the Java file won't produce a proof obligation since there are no method contracts; in any case, all examples are relational, and therefore a more complex proof obligation is set up manually in the problem definition files.