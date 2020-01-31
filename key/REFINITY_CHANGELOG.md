REFINITY CHANGES
================

## XXX (v0.9.4) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Supporting postconditions via standard "ensures" for break and continue behavior
  * Stability fixes in the user interface

## 2019-12-29 (v0.9.3) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Changed AE rules: Initialization of result and exception objects in abstract update scope. Breaks
    backwards compatibility with existing proofs!
  * Adapted Strategies: Simplification of abstract updates has now same priority as simplification of
    concrete update. Leads to a performance boost.

## 2019-12-06 (v0.9.2) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Bug fixes in conversion to KeY file
  * Different behavior when pressing Ctrl+S for yet unsaved model: Show dialog instead of status message
  * Fixed bug in pre- postcondition relation fields about unrecognized symbols which actually have been added

## 2019-12-06 (v0.9.1) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Supporting relational preconditions
  * Better heap simplification (abstract update simplification for select expressions, removing ineffective anonymizations) 

## 2019-12-05 (v0.9) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * JML Support for relation to verify
  * Fixed compilation bug when using Java 8
  * Started KeY-independent versioning, displaying version number in title