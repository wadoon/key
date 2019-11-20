example.name = Extract Prefix
example.path = Abstract Execution/Consolidate Duplicate Conditional Fragments/
example.file = consolidateDuplicateConditionalFragments.aer

The standard "Extract Prefix" variant of Martin Fowler's "Consolidate Duplicate Conditional Fragments" refactoring. Abrupt completion of guard and extracted fragment is allowed, but mutually exclusive. Various constraints on the frames and footprints of participating abstract program elements have to be imposed.