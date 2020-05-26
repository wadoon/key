# Notes on  verification of floating-point programs in KeY

In order to analyze programs containing basic floating-point arithmetic: 

1)	Check out the *daisyNewSMT* branch in they KeY repository, then build and run KeY. The revision number used for  the evaluation in the paper is "56724606dcdd33607715a93ab8f07f80e87ca214". 

2)	Make sure to use KeY in the *strictfp* mode. In KeY menu select *floatRules:assumeStrictfp* in Options -> Taclet *Options -> floatRules*  in KeY menu. 

3)	You have an option to exclude the quantified formulas from the SMT translations. You can choose to exclude them by deselecting  *use an explicit type hierarchy* and *enable quantifiers in SMT translation* in *Options -> SMT Solvers Options  -> SMT-Translation*. 

4)	If your program contains the square root function, choose to use the precise implementation of the square root function in the SMT translation (fp.sqrt) by selecting *disable square root axiomatizing in SMT translation*  in *Options -> SMT Solvers Options  -> SMT-Translation*. Deselecting this option results in axiomatization of the square root function. 

5)	Examples of programs with floating-point arithmetic are in *keyDaisy/benchmarks* and *keyDaisy/examples* in https://gitlab.mpi-sws.org/AVA/keydaisy. The expected verification results are in *keyDaisy/results/smtResults.md* for most programs. 

6) Inorder to use the modular SMT-LIB translation, in the KeY menu select sovlers with the *(New TL)* text in front. 
7) For the experiments in the paper we used Z3(4.8.5), CVC4(1.7) and MathSAT(5.5.4) with "-in -smt2", "--no-print-success -m --interactive --lang smt2" and "-proof_generation=FALSE  -input=smt2" respectively as parameters. To set parameters for the solvers select  Options -> SMT Solvers Options in the KeY menu and then select and set parameters for a solver. 

In order to analyze programs containing transcendental functions: 

*	If you choose to axiomatize the transcendental functions in the SMT translation: 

    1. The axioms (in the SMT-LIB format) exist in /Users/rosaabbasi/Desktop/work/keyDaisyProject/key/key/key/key.core/src/main/resources/de/uka/ilkd/key/smt/newsmt2/FloatHandler.preamble.xml. They are mostly adapted from the IEEE 754 standard and the Math.java documentation in https://docs.oracle.com/javase/8/docs/api/java/lang/Math.html. You can also add new axioms in the same file using the *.axioms tags. 

    2. Load a program into KeY. Generate the proof obligations as always and then apply SMT solvers as always. 

*	If you choose to axiomatize the transcendental functions as Taclet rules in KeY: 

    1. First you need to comment out the axioms in the *.axioms tags in 

    /Users/rosaabbasi/Desktop/work/keyDaisyProject/key/key/key/key.core/src/main/resources/de/uka/ilkd/key/smt/newsmt2/FloatHandler.preamble.xml

    You can also do this only for the functions that are used in your example. 

    *** Don’t forget to rerun KeY afterwards ***

    2. The Taclet rules are in:
    /Users/rosaabbasi/Desktop/work/keyDaisyProject/key/key/key/key.core/src/main/resources/de/uka/ilkd/key/proof/rules/floatRulesCommon.key

    You can also add your own rules in the same file. 

    3. Load the program into KeY, then run KeY, after the automatic rule application is done, In the proof obligations, select a transcendental function and apply a feasible taclet rule. Apply as many rules as needed. Then, use a SMT solver to produce the verification results.  

*	Benchmarks containing transcendental functions are in in *keyDaisy/benchmarks* and *keyDaisy/examples*. For the most parts the programs in both packages are the same. The difference is that there is more information commented in the class files in *keyDaisy/examples*. For example, the set of Taclet rules that can be applies to reproduce the verification results are commented in the class files in *keyDaisy/examples*.



