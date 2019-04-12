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
 * we formalize a "rollback" for a Skolem location set; this undoes all the
 * changes of "Normal" in the case of exceptional termination. The Rollback APS
 * has to overwrite the location set in question (no "maybe" possible").
 *
 * @author Dominic Steinhoefel
 */
public class ReplaceExceptionWithTest {
    //@ declares \dl_args;
    public Object before(Object res, boolean throwsExc) {
        //@ declares \dl_localsInit, \dl_varsToRollBack;
        //@ assignable \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        //@ accessible \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        { \abstract_statement Init; }

        try {
            //@ declares \dl_localsNormal;
            //@ assignable \dl_localsNormal, \dl_varsToRollBack;
            //@ accessible \dl_localsInit, \dl_localsNormal, \dl_args, res;
            //@ exceptional_behavior requires throwsExc;
            { \abstract_statement Normal; }
        } catch (Throwable t) {
            //@ assignable \dl_hasTo(\dl_varsToRollBack);
            //@ accessible \nothing;
            { \abstract_statement Rollback; }
            
            //@ declares \dl_localsExceptional;
            //@ assignable \dl_localsInit, \dl_localsExceptional, \dl_args, res, \dl_varsToRollBack;
            //@ accessible \dl_localsInit, \dl_localsExceptional, \dl_args, res, \dl_varsToRollBack;
            { \abstract_statement Exceptional; }
        }

        //@ declares \dl_localsAfter;
        //@ assignable \dl_localsAfter, \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        //@ accessible \dl_localsAfter, \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        { \abstract_statement After; }
        
        return res;
    }
    
    //@ declares \dl_args;
    public Object after(Object res, boolean throwsExc) {
        //@ declares \dl_localsInit, \dl_varsToRollBack;
        //@ assignable \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        //@ accessible \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        { \abstract_statement Init; }

        if (!throwsExc) {
            //@ declares \dl_localsNormal;
            //@ assignable \dl_localsNormal, \dl_varsToRollBack;
            //@ accessible \dl_localsInit, \dl_localsNormal, \dl_args, res;
            //@ exceptional_behavior requires throwsExc;
            { \abstract_statement Normal; }
        } else {
            //@ assignable \dl_hasTo(\dl_varsToRollBack);
            //@ accessible \nothing;
            { \abstract_statement Rollback; }
            
            //@ declares \dl_localsExceptional;
            //@ assignable \dl_localsInit, \dl_localsExceptional, \dl_args, res, \dl_varsToRollBack;
            //@ accessible \dl_localsInit, \dl_localsExceptional, \dl_args, res, \dl_varsToRollBack;
            { \abstract_statement Exceptional; }
        }

        //@ declares \dl_localsAfter;
        //@ assignable \dl_localsAfter, \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        //@ accessible \dl_localsAfter, \dl_localsInit, \dl_args, res, \dl_varsToRollBack;
        { \abstract_statement After; }
        
        return res;
    }
}