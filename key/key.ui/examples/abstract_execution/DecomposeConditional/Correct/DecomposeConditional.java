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
 * A model of the "decompose conditional" refactoring by M. Fowler. It is
 * actually a special case of the extract method refactoring, where the guard of
 * an if statement, the then and else branch are extracted to individual
 * methods.
 * 
 * The example shows how abstract expressions currently have to be
 * "pre-processed" such that we can make use of the abstract placeholder
 * statements. Instead of directly defining an abstract expression, a program
 * variable is chosen, and a placeholder statement assigning that variable
 * introduced before. Note that those variables have to be "global" for the
 * relational verification to work due to complications with variable renaming
 * in KeY.
 * 
 * Note that the guard expression may not return (this also leads to an error
 * during proof execution), as well as for the usual extract method refactoring.
 * If the result type of the outer method (before/after) is not boolean, this
 * will also lead to an error during proof construction.
 *
 * @author Dominic Steinhoefel
 */
public class DecomposeConditional {
    //@ declares \dl_args;
    public Object before(Object res, boolean guard, Object tmp) {
        //@ assignable \dl_hasTo(guard);
        //@ accessible \dl_heap, \dl_args, res, guard;
        //@ return_behavior requires false;
        { abstract_statement GuardExpr; }
        
        if (guard) {
            //@ declares \dl_localsThen;
            //@ assignable \dl_heap, \dl_localsThen, \dl_hasTo(tmp);
            //@ accessible \dl_heap, \dl_localsThen, tmp, \dl_args, res, guard;
            //@ return_behavior requires false;
            { abstract_statement ThenProg; }
        } else {
            //@ declares \dl_localsElse;
            //@ assignable \dl_heap, \dl_localsElse, \dl_hasTo(tmp);
            //@ accessible \dl_heap, \dl_localsElse, tmp, \dl_args, res, guard;
            //@ return_behavior requires false;
            { abstract_statement ElseProg; }
        }

        //@ declares \dl_localsPostProc;
        //@ assignable \dl_heap, \dl_localsPostProc, tmp, \dl_args, res, guard;
        //@ accessible \dl_heap, \dl_localsPostProc, tmp, \dl_args, res, guard;
        { abstract_statement PostProc; }
        
        return res;
    }

    //@ declares \dl_args;
    public Object after(Object res, boolean guard, Object tmp) {
        guard = extractedGuard(res, guard);
        
        if (guard) {
            tmp = extractedThen(res, guard, tmp);
        } else {
            tmp = extractedElse(res, guard, tmp);
        }

        //@ declares \dl_localsPostProc;
        //@ assignable \dl_heap, \dl_localsPostProc, tmp, \dl_args, res, guard;
        //@ accessible \dl_heap, \dl_localsPostProc, tmp, \dl_args, res, guard;
        { abstract_statement PostProc; }
        
        return res;
    }

    //@ declares \dl_final(\dl_args);
    private boolean extractedGuard(final Object res, boolean guard) {
        //@ assignable \dl_hasTo(guard);
        //@ accessible \dl_heap, \dl_args, res, guard;
        //@ return_behavior requires false;
        { abstract_statement GuardExpr; }

        return guard;
    }

    //@ declares \dl_final(\dl_args);
    private Object extractedThen(final Object res, boolean guard, Object tmp) {
        //@ declares \dl_localsThen;
        //@ assignable \dl_heap, \dl_localsThen, \dl_hasTo(tmp);
        //@ accessible \dl_heap, \dl_localsThen, tmp, \dl_args, res, guard;
        //@ return_behavior requires false;
        { abstract_statement ThenProg; }
        
        return tmp;
    }

    //@ declares \dl_final(\dl_args);
    private Object extractedElse(final Object res, boolean guard, Object tmp) {
        //@ declares \dl_localsElse;
        //@ assignable \dl_heap, \dl_localsElse, \dl_hasTo(tmp);
        //@ accessible \dl_heap, \dl_localsElse, tmp, \dl_args, res, guard;
        //@ return_behavior requires false;
        { abstract_statement ElseProg; }
        
        return tmp;
    }
}