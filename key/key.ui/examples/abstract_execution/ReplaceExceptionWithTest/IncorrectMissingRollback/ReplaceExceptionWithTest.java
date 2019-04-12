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
 * terminates with an exception; "Exceptional" might not recover from
 * that. Therefore, the version below does not work: There remain two
 * open proof goals for the case where "Normal" terminates with an exception
 * (and everything else works without abrupt termination).
 *
 * @author Dominic Steinhoefel
 */
public class ReplaceExceptionWithTest {
    //@ declares \dl_args;
    public Object before(Object res, boolean throwsExc) {
        //@ declares \dl_localsInit;
        //@ assignable \dl_localsInit, \dl_args, res;
        //@ accessible \dl_localsInit, \dl_args, res;
        { \abstract_statement Init; }

        try {
            //@ declares \dl_localsNormal;
            //@ assignable \dl_localsNormal, \dl_localsInit, \dl_args, res;
            //@ accessible \dl_localsNormal, \dl_localsInit, \dl_args, res;
            //@ exceptional_behavior requires throwsExc;
            { \abstract_statement Normal; }
        } catch (Throwable t) {
            //@ declares \dl_localsExceptional;
            //@ assignable \dl_localsInit, \dl_localsExceptional, \dl_args, res;
            //@ accessible \dl_localsInit, \dl_localsExceptional, \dl_args, res;
            { \abstract_statement Exceptional; }
        }

        //@ declares \dl_localsAfter;
        //@ assignable \dl_localsAfter, \dl_localsInit, \dl_localsInit, \dl_args, res;
        //@ accessible \dl_localsAfter, \dl_localsInit, \dl_localsInit, \dl_args, res;
        { \abstract_statement After; }
        
        return res;
    }
    
    //@ declares \dl_args;
    public Object after(Object res, boolean throwsExc) {
        //@ declares \dl_localsInit;
        //@ assignable \dl_localsInit, \dl_args, res;
        //@ accessible \dl_localsInit, \dl_args, res;
        { \abstract_statement Init; }

        if (!throwsExc) {
            //@ declares \dl_localsNormal;
            //@ assignable \dl_localsNormal, \dl_localsInit, \dl_args, res;
            //@ accessible \dl_localsNormal, \dl_localsInit, \dl_args, res;
            //@ exceptional_behavior requires throwsExc;
            { \abstract_statement Normal; }
        } else {
            //@ declares \dl_localsExceptional;
            //@ assignable \dl_localsInit, \dl_localsExceptional, \dl_args, res;
            //@ accessible \dl_localsInit, \dl_localsExceptional, \dl_args, res;
            { \abstract_statement Exceptional; }
        }

        //@ declares \dl_localsAfter;
        //@ assignable \dl_localsAfter, \dl_localsInit, \dl_localsInit, \dl_args, res;
        //@ accessible \dl_localsAfter, \dl_localsInit, \dl_localsInit, \dl_args, res;
        { \abstract_statement After; }
        
        return res;
    }
}