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
 * A model of the "consolidate duplicate conditional fragments" refactoring by
 * M. Fowler. In this variant, a postfix is pulled out of a try-catch block and
 * put after the block. From Fowler's descriptions, it it not clear whether
 * "move it [Postfix] to the final block" refers to the "finally" block or is
 * just another way to describe moving it after the try-catch. If "finally" was
 * the intended meaning, interestingly that actually complicates the
 * refactoring, finally blocks are even executed after returns.
 * 
 * Discovered: We have to forbid Postfix to throw an exception; otherwise, the
 * additional effects of CatchProg prevent closing the goal.
 *
 * @author Dominic Steinhoefel
 */
public class ConsolidateDuplicateConditionalFragments {
    //@ declares \dl_args;
    public Object before(Object res) {
        try {
            //@ declares \dl_localsTryProg;
            //@ assignable res, \dl_heap, \dl_localsTryProg, \dl_args;
            //@ accessible res, \dl_heap, \dl_localsTryProg, \dl_args;
            { \abstract_statement TryProg; }
            
            //@ declares \dl_localsPostfix;
            //@ assignable res, \dl_heap, \dl_localsPostfix, \dl_args;
            //@ accessible res, \dl_heap, \dl_localsPostfix, \dl_args;
            //@ exceptional_behavior requires false;
            { \abstract_statement Postfix; }
        }
        catch (Throwable t) {
            //@ declares \dl_localsCatchProg;
            //@ assignable res, \dl_heap, \dl_localsCatchProg, \dl_args;
            //@ accessible res, \dl_heap, \dl_localsCatchProg, \dl_args;
            { \abstract_statement CatchProg; }
            
            //@ declares \dl_localsPostfix;
            //@ assignable res, \dl_heap, \dl_localsPostfix, \dl_args;
            //@ accessible res, \dl_heap, \dl_localsPostfix, \dl_args;
            //@ exceptional_behavior requires false;
            { \abstract_statement Postfix; }
        }

        return res;
    }

    //@ declares \dl_args;
    public Object after(Object res) {
        try {
            //@ declares \dl_localsTryProg;
            //@ assignable res, \dl_heap, \dl_localsTryProg, \dl_args;
            //@ accessible res, \dl_heap, \dl_localsTryProg, \dl_args;
            { \abstract_statement TryProg; }
        }
        catch (Throwable t) {
            //@ declares \dl_localsCatchProg;
            //@ assignable res, \dl_heap, \dl_localsCatchProg, \dl_args;
            //@ accessible res, \dl_heap, \dl_localsCatchProg, \dl_args;
            { \abstract_statement CatchProg; }
        }
        
        //@ declares \dl_localsPostfix;
        //@ assignable res, \dl_heap, \dl_localsPostfix, \dl_args;
        //@ accessible res, \dl_heap, \dl_localsPostfix, \dl_args;
        //@ exceptional_behavior requires false;
        { \abstract_statement Postfix; }

        return res;
    }
}