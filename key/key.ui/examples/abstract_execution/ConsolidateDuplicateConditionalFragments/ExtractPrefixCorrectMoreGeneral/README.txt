example.name = Extract Prefix (Most General)
example.path = Abstract Execution/Consolidate Duplicate Conditional Fragments/
example.file = consolidateDuplicateConditionalFragments.aer

The standard "Extract Prefix" variant of Martin Fowler's "Consolidate Duplicate Conditional Fragments" refactoring in its currently most general variant. Locations of interest are abstract and not just a single result variable; abrupt completion of guard and extracted fragment is allowed, but mutually exclusive.