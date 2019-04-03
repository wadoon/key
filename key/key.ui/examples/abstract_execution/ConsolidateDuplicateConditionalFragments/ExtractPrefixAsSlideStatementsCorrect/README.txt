example.name = Extract Prefix
example.path = Abstract Execution/Consolidate Duplicate Conditional Fragments/
example.file = consolidateDuplicateConditionalFragmentsPrefixCorrect.key
example.additionalFile.1 = ConsolidateDuplicateConditionalFragments.java

The "Extract Prefix" variant of Martin Fowler's "Decompose Conditional Fragments" refactoring. Here, one has to specify that the if condition is independent of the prefix, and that it does not throw an exception when the prefix does also not terminated normally.