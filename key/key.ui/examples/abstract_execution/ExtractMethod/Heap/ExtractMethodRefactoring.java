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
 * A model of the "extract method" refactoring by M. Fowler. Note that this
 * refactoring is only correct in presence of the additional specifications.
 * Most importantly, Q must not return.
 *
 * @author Dominic Steinhoefel
 */
public class ExtractMethodRefactoring {
    private Object tmp;
    
    //@ declares \dl_args;
    public Object before(Object res) {
        //@ declares \dl_localsP;
        //@ assignable \dl_localsP, \dl_args, this.tmp, res;
        //@ accessible \dl_localsP, \dl_args, this.tmp, res;
        { abstract_statement P; }

        //@ declares \dl_localsQ;
        //@ assignable \dl_hasTo(this.tmp), \dl_localsQ;
        //@ accessible \dl_localsP, \dl_localsQ, \dl_args, this.tmp, res;
        //@ return_behavior requires false;
        { abstract_statement Q; }

        //@ declares \dl_localsR;
        //@ assignable \dl_localsP, \dl_localsR, \dl_args, this.tmp, res;
        //@ accessible \dl_localsP, \dl_localsR, \dl_args, this.tmp, res;
        { abstract_statement R; }

        return res;
    }

    //@ declares \dl_args;
    public Object after(Object res) {
        //@ declares \dl_localsP;
        //@ assignable \dl_localsP, \dl_args, this.tmp, res;
        //@ accessible \dl_localsP, \dl_args, this.tmp, res;
        { abstract_statement P; }

        extracted(res);

        //@ declares \dl_localsR;
        //@ assignable \dl_localsP, \dl_localsR, \dl_args, this.tmp, res;
        //@ accessible \dl_localsP, \dl_localsR, \dl_args, this.tmp, res;
        { abstract_statement R; }

        return res;
    }

    //@ declares \dl_final(\dl_localsP), \dl_final(\dl_args);
    private void extracted(final Object res) {
        //@ declares \dl_localsQ;
        //@ assignable \dl_hasTo(this.tmp), \dl_localsQ;
        //@ accessible \dl_localsP, \dl_localsQ, \dl_args, this.tmp, res;
        //@ return_behavior requires false;
        { abstract_statement Q; }
    }
}