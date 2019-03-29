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
 * A model of the "slide statement" refactoring by M. Fowler.
 * 
 * The insight here is that two statements may only be moved if they do not
 * assign to locations that the other one reads. Therefore, abstract statements
 * B, C, and D assign to distinct location sets. The model below may be rendered
 * a little more liberal by defining distinct parts of the heap (currently not
 * possible) and the method arguments (this is possible).
 *
 * @author Dominic Steinhoefel
 */
public class SlideStatements {
    //@ declares \dl_args;
    public Object before(Object res) {
        //@ declares \dl_localsA;
        //@ assignable \dl_heap, \dl_localsA, \dl_args, res;
        //@ accessible \dl_heap, \dl_localsA, \dl_args, res;
        { abstract_statement A; }
        
        //@ declares \dl_localsB;
        //@ assignable \dl_localsB;
        //@ accessible \dl_heap, \dl_localsB, \dl_args, res;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement B; }
        
        //@ declares \dl_localsC;
        //@ assignable \dl_localsC;
        //@ accessible \dl_heap, \dl_localsC, \dl_args, res;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement C; }
        
        //@ declares \dl_localsD;
        //@ assignable \dl_localsD;
        //@ accessible \dl_heap, \dl_localsD, \dl_args, res;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement D; }
        
        //@ declares \dl_localsE;
        //@ assignable \dl_heap, \dl_localsA, \dl_localsB, \dl_localsC, \dl_localsD, \dl_localsE, \dl_args, res;
        //@ accessible \dl_heap, \dl_localsA, \dl_localsB, \dl_localsC, \dl_localsD, \dl_localsE, \dl_args, res;
        { abstract_statement E; }
        
        return res;
    }

    //@ declares \dl_args;
    public Object after(Object res) {
        //@ declares \dl_localsA;
        //@ assignable \dl_heap, \dl_localsA, \dl_args, res;
        //@ accessible \dl_heap, \dl_localsA, \dl_args, res;
        { abstract_statement A; }
        
        //@ declares \dl_localsD;
        //@ assignable \dl_localsD;
        //@ accessible \dl_heap, \dl_localsD, \dl_args, res;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement D; }
        
        //@ declares \dl_localsC;
        //@ assignable \dl_localsC;
        //@ accessible \dl_heap, \dl_localsC, \dl_args, res;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement C; }
        
        //@ declares \dl_localsB;
        //@ assignable \dl_localsB;
        //@ accessible \dl_heap, \dl_localsB, \dl_args, res;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement B; }
        
        //@ declares \dl_localsE;
        //@ assignable \dl_heap, \dl_localsA, \dl_localsB, \dl_localsC, \dl_localsD, \dl_localsE, \dl_args, res;
        //@ accessible \dl_heap, \dl_localsA, \dl_localsB, \dl_localsC, \dl_localsD, \dl_localsE, \dl_args, res;
        { abstract_statement E; }
        
        return res;
    }
}