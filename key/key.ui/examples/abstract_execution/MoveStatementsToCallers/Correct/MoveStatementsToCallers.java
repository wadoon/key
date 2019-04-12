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
 * A model of the "Move Statements to Callers" (or, inversely, "Move Statements
 * into Function") refactoring by M. Fowler.
 *
 * @author Dominic Steinhoefel
 */
public class MoveStatementsToCallers {
    //@ declares \dl_args;
    public Object before(Object res) {
        calledBefore();
        
        //@ declares \dl_localsB;
        //@ assignable \dl_heap, \dl_localsB, \dl_args, res;
        //@ accessible \dl_heap, \dl_localsB, \dl_args, res;
        { \abstract_statement B; }
        
        return res;
    }

    //@ declares \dl_final(\dl_args);
    private boolean calledBefore() {
        //@ declares \dl_localsC;
        //@ assignable \dl_heap, \dl_localsC;
        //@ accessible \dl_heap, \dl_localsC, \dl_args;
        //@ return_behavior requires false;
        { \abstract_statement C; }
        
        //@ declares \dl_localsA;
        //@ assignable \dl_heap, \dl_localsA;
        //@ accessible \dl_heap, \dl_localsA, \dl_args;
        //@ return_behavior requires false;
        { \abstract_statement A; }

        return;
    }

    //@ declares \dl_args;
    public Object after(Object res) {
        calledAfter();
        
        //@ declares \dl_localsA;
        //@ assignable \dl_heap, \dl_localsA;
        //@ accessible \dl_heap, \dl_localsA, \dl_args;
        //@ return_behavior requires false;
        { \abstract_statement A; }
        
        //@ declares \dl_localsB;
        //@ assignable \dl_heap, \dl_localsB, \dl_args, res;
        //@ accessible \dl_heap, \dl_localsB, \dl_args, res;
        { \abstract_statement B; }
        
        return res;
    }

    //@ declares \dl_final(\dl_args);
    private boolean calledAfter() {
        //@ declares \dl_localsC;
        //@ assignable \dl_heap, \dl_localsC;
        //@ accessible \dl_heap, \dl_localsC, \dl_args;
        //@ return_behavior requires false;
        { \abstract_statement C; }

        return;
    }

}