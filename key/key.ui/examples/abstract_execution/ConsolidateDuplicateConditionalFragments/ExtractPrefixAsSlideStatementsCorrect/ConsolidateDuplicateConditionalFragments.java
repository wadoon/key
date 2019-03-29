// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/**
 * A model of a variant of the "consolidate duplicate conditional fragments"
 * refactoring by M. Fowler. Note that this refactoring is *not* correct without
 * the additional specifications, since P might access the variable b.
 * 
 * This version has a complex abstract expression as guard of the if statement.
 * As such, it becomes more obvious that this is actually an instance of the
 * "Slide Statement" refactoring of the 2nd edition of Fowler's book, as which
 * it is also described in the book. In contrast of the variant with just a
 * simple variable as guard, the abstract expression (modeled by an abstract
 * placeholder statement) may not read from the heap if it can also be changed
 * by the statement moved before, or conversely, if it may change the heap, then
 * that statement may not read from it.
 * 
 * This example helped to pinpoint yet another subtlety of the consolidate
 * duplicate conditional fragements refactoring: If the guard throws an
 * exception and the pulled out prefix returns, then the refactoring is *not*
 * legal for the differing reasons of method termination. So we either (1) have
 * to forbid P to terminate or (2) Init to throw an exception. We opted for (2)
 * here.
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    //@ declares \dl_params;
    public int before(Object res, boolean b) {
        //@ declares \dl_localsInit;
        //@ assignable \dl_localsInit, \dl_hasTo(b);
        //@ accessible \dl_localsInit, \dl_params;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires \dl_initThrows;
        { abstract_statement Init; }
        
        if (b) {
            //@ declares \dl_localsP;
            //@ assignable \dl_heap, \dl_localsP, res;
            //@ accessible \dl_heap, \dl_localsP, res, \dl_params;
            //@ return_behavior requires \dl_pReturns;
            //@ exceptional_behavior requires \dl_pThrows;
            { abstract_statement P; }
            
            //@ declares \dl_localsQ1;
            //@ assignable \dl_allLocs;
            //@ accessible \dl_allLocs;
            { abstract_statement Q1; }
        }
        else {
            //@ declares \dl_localsP;
            //@ assignable \dl_heap, \dl_localsP, res;
            //@ accessible \dl_heap, \dl_localsP, res, \dl_params;
            { abstract_statement P; }

            //@ declares \dl_localsQ2;
            //@ assignable \dl_allLocs;
            //@ accessible \dl_allLocs;
            { abstract_statement Q2; }
        }

        return res;
    }

    //@ declares \dl_params;
    public int after(Object res, boolean b) {
        //@ declares \dl_localsP;
        //@ assignable \dl_heap, \dl_localsP, res;
        //@ accessible \dl_heap, \dl_localsP, res, \dl_params;
        //@ return_behavior requires \dl_pReturns;
        //@ exceptional_behavior requires \dl_pThrows;
        { abstract_statement P; }
        
        //@ declares \dl_localsInit;
        //@ assignable \dl_localsInit, \dl_hasTo(b);
        //@ accessible \dl_localsInit, \dl_params;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires \dl_initThrows;
        { abstract_statement Init; }
        
        if (b) {
            //@ declares \dl_localsQ1;
            //@ assignable \dl_allLocs;
            //@ accessible \dl_allLocs;
            { abstract_statement Q1; }
        }
        else {
            //@ declares \dl_localsQ2;
            //@ assignable \dl_allLocs;
            //@ accessible \dl_allLocs;
            { abstract_statement Q2; }
        }

        return res;
    }
}