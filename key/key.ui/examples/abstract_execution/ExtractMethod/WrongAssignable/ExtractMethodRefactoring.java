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
 * A model of the "extract method" refactoring by M. Fowler. In this version,
 * the specification of Q permits accessing more variables than the tmp variable
 * and the heap, therefore, the refactoring is not permitted.
 *
 * @author Dominic Steinhoefel
 */
public class ExtractMethodRefactoring {
    //@ declares \dl_args;
    public Object before(Object res, Object tmp) {
        //@ declares \dl_localsP;
        //@ assignable \dl_heap, \dl_localsP, \dl_args, tmp, res;
        //@ accessible \dl_heap, \dl_localsP, \dl_args, tmp, res;
        { abstract_statement P; }

        //@ declares \dl_localsQ;
        //@ assignable \dl_heap, \dl_localsQ, tmp, res;
        //@ accessible \dl_heap, \dl_localsP, \dl_localsQ, \dl_args, tmp, res;
        //@ return_behavior requires false;
        { abstract_statement Q; }

        //@ declares \dl_localsR;
        //@ assignable \dl_heap, \dl_localsP, \dl_localsR, \dl_args, tmp, res;
        //@ accessible \dl_heap, \dl_localsP, \dl_localsR, \dl_args, tmp, res;
        { abstract_statement R; }

        return res;
    }

    //@ declares \dl_args;
    public void after(Object res, Object tmp) {
        //@ declares \dl_localsP;
        //@ assignable \dl_heap, \dl_localsP, \dl_args, tmp, res;
        //@ accessible \dl_heap, \dl_localsP, \dl_args, tmp, res;
        { abstract_statement P; }

        tmp = extracted(res, tmp);

        //@ declares \dl_localsR;
        //@ assignable \dl_heap, \dl_localsP, \dl_localsR, \dl_args, tmp, res;
        //@ accessible \dl_heap, \dl_localsP, \dl_localsR, \dl_args, tmp, res;
        { abstract_statement R; }

        return res;
    }

    //@ declares \dl_final(\dl_localsP), \dl_final(\dl_args);
    private Object extracted(Object res, Object tmp) {
        //@ declares \dl_localsQ;
        //@ assignable \dl_heap, \dl_localsQ, tmp, res;
        //@ accessible \dl_heap, \dl_localsP, \dl_localsQ, \dl_args, tmp, res;
        //@ return_behavior requires false;
        { abstract_statement Q; }

        return tmp;
    }
}