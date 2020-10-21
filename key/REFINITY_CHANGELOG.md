
REFINITY CHANGES
================

## 2020-10-21 (v0.9.7) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Syntax checking for APE specifications
  * Instantiation checking: Check whether a concrete program is an instance of
    an abstract one. Early testing face, only programmatic access.
  * Bugfixes (e.g., no saving necessary before validating a proof)

## 2020-06-12 (v0.9.6) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Added certificate checking: Validate a saved proof bundle for a model.

## 2020-06-05 (v0.9.5) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Automatic addition of empty block { ; } after ae_constraint. Manual addition of empty block
    therefore no longer necessary.

## 2020-04-24 (v0.9.4) Dominic Steinhoefel <steinhoefel@cs.tu-darmstadt.de>

  * Supporting postconditions via standard "ensures" for break and continue behavior
  * Stability fixes in the user interface
  * Saving recently opened REFINITY models
  * New \field and \progvar JML types for advanced framing conditions
  * Support for abstract location sets with parameters (like, e.g., "subFrame(int)")
    
    NOTE: This change breaks backwards compatibility of .aer files, as abstract location
    sets can now be parametrized and are realized as function declarations (what they
    in fact always were).

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