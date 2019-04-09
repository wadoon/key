example.name = Manually Unrolled Original Program
example.path = Abstract Execution/Remove Control Flag/
example.file = removeControlFlag.key
example.additionalFile.1 = RemoveControlFlag.java
example.proofFile = removeControlFlag.proof

A model of Martin Fowler's "Remove Control Flag" refactoring. This is a more complex example with a loop, in which the original program takes one more iteration than the refactored one. Therefore, a "loop harmonization" technique, in this case a variant of loop unrolling, is applied to deal with this. We are using a two-step process here, i.e. prove equivalence of the original with an intermediate version, and of that with the refactored version.