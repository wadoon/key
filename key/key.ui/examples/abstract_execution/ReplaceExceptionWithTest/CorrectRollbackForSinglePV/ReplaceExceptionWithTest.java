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
 * A model of the "Move Exception with Test" refactoring by M. Fowler.
 * 
 * Discovered problem: Program "Normal" can change the state before it
 * terminates with an exception; "Exceptional" might not recover from that. Here
 * we only let "Normal" assign a single program variable which we reset in case
 * of exceptional termination. In another example, we perform the reset for a
 * whole Skolem location set.
 *
 * @author Dominic Steinhoefel
 */
public class ReplaceExceptionWithTest {
    //@ declares \dl_args;
    public Object before(Object res, Object pv, boolean throwsExc) {
        //@ declares \dl_localsInit;
        //@ assignable \dl_localsInit, \dl_args, res, pv;
        //@ accessible \dl_localsInit, \dl_args, res, pv;
        { abstract_statement Init; }

        try {
            //@ declares \dl_localsNormal;
            //@ assignable \dl_localsNormal, pv;
            //@ accessible \dl_localsInit, \dl_localsNormal, \dl_args, res;
            //@ exceptional_behavior requires throwsExc;
            { abstract_statement Normal; }
        } catch (Throwable t) {
            pv = null;
            
            //@ declares \dl_localsExceptional;
            //@ assignable \dl_localsInit, \dl_localsExceptional, \dl_args, res, pv;
            //@ accessible \dl_localsInit, \dl_localsExceptional, \dl_args, res, pv;
            { abstract_statement Exceptional; }
        }

        //@ declares \dl_localsAfter;
        //@ assignable \dl_localsAfter, \dl_localsInit, \dl_args, res, pv;
        //@ accessible \dl_localsAfter, \dl_localsInit, \dl_args, res, pv;
        { abstract_statement After; }
        
        return res;
    }
    
    //@ declares \dl_args;
    public Object after(Object res, Object pv, boolean throwsExc) {
        //@ declares \dl_localsInit;
        //@ assignable \dl_localsInit, \dl_args, res, pv;
        //@ accessible \dl_localsInit, \dl_args, res, pv;
        { abstract_statement Init; }

        if (!throwsExc) {
            //@ declares \dl_localsNormal;
            //@ assignable \dl_localsNormal, pv;
            //@ accessible \dl_localsInit, \dl_localsNormal, \dl_args, res;
            //@ exceptional_behavior requires throwsExc;
            { abstract_statement Normal; }
        } else {
            pv = null;
            
            //@ declares \dl_localsExceptional;
            //@ assignable \dl_localsInit, \dl_localsExceptional, \dl_args, res, pv;
            //@ accessible \dl_localsInit, \dl_localsExceptional, \dl_args, res, pv;
            { abstract_statement Exceptional; }
        }

        //@ declares \dl_localsAfter;
        //@ assignable \dl_localsAfter, \dl_localsInit, \dl_args, res, pv;
        //@ accessible \dl_localsAfter, \dl_localsInit, \dl_args, res, pv;
        { abstract_statement After; }
        
        return res;
    }
}