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
 * A model of the "split loop" refactoring by M. Fowler.
 * 
 * We have to disallow LoopBodyA to continue because otherwise, it would have
 * to establish also the loop invariant for LoopBodyB.
 *
 * @author Dominic Steinhoefel
 */
public class SplitLoopRefactoring {
    public Object before(Object res, final Object[] loopArgs, Object obj, int i) {
        //@ declares \dl_localsPreProc;
        //@ assignable \dl_heap, \dl_localsPreProc, res;
        //@ accessible \dl_heap, \dl_localsPreProc, res, loopArgs;
        { \abstract_statement PreProc; }
        
        //@ declares \dl_outA;
        //@ assignable \dl_outA;
        //@ accessible \nothing;
        { \abstract_statement InitA; }

        //@ declares \dl_outB;
        //@ assignable \dl_outB;
        //@ accessible \nothing;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { \abstract_statement InitB; }
      
        i = -1;
        
        /*@ loop_invariant i >= -1 && i <= loopArgs.length;
          @ assignable \strictly_nothing;
          @ decreases loopArgs.length - i;
          @*/
        while (++i < loopArgs.length) {
            obj = loopArgs[i];
            
            //@ declares \dl_localsLoopBodyA;
            //@ assignable \dl_localsLoopBodyA, \dl_outA;
            //@ accessible \dl_localsLoopBodyA, obj, res, \dl_localsPreProc;
            //@ break_behavior requires false;
            //@ continue_behavior requires false;
            { \abstract_statement LoopBodyA; }
            
            //@ declares \dl_localsLoopBodyB;
            //@ assignable \dl_localsLoopBodyB, \dl_outB;
            //@ accessible \dl_localsLoopBodyB, obj, res, \dl_localsPreProc;
            //@ return_behavior requires false;
            //@ exceptional_behavior requires false;
            //@ break_behavior requires false;
            { \abstract_statement LoopBodyB; }
        }

        //@ declares \dl_localsPostProcA;
        //@ assignable \dl_localsPostProcA;
        //@ accessible \dl_heap, \dl_localsPostProcA, res, \dl_outA, \dl_localsPreProc;
        { \abstract_statement PostProcA; }

        //@ declares \dl_localsPostProcB;
        //@ assignable \dl_heap, \dl_localsPostProcB;
        //@ accessible \dl_heap, \dl_localsPostProcB, res, \dl_outB, \dl_localsPreProc;
        { \abstract_statement PostProcB; }

        //@ declares \dl_localsPostProc;
        //@ assignable \dl_heap, \dl_localsPostProc, \dl_localsPreProc, \dl_outA, \dl_outB, \dl_localsPostProcA, \dl_localsPostProcB, res;
        //@ accessible \dl_heap, \dl_localsPostProc, \dl_localsPreProc, \dl_outA, \dl_outB, \dl_localsPostProcA, \dl_localsPostProcB, res;
        { \abstract_statement PostProc; }

        return res;
    }
    
    public Object after(Object res, final Object[] loopArgs, Object obj, int i) {
        //@ declares \dl_localsPreProc;
        //@ assignable \dl_heap, \dl_localsPreProc, res;
        //@ accessible \dl_heap, \dl_localsPreProc, res, loopArgs;
        { \abstract_statement PreProc; }
        
        //@ declares \dl_outA;
        //@ assignable \dl_outA;
        //@ accessible \nothing;
        { \abstract_statement InitA; }

        i = -1;
        
        /*@ loop_invariant i >= -1 && i <= loopArgs.length;
          @ assignable \strictly_nothing;
          @ decreases loopArgs.length - i;
          @*/
        while (++i < loopArgs.length) {
            obj = loopArgs[i];
            
            //@ declares \dl_localsLoopBodyA;
            //@ assignable \dl_localsLoopBodyA, \dl_outA;
            //@ accessible \dl_localsLoopBodyA, obj, res, \dl_localsPreProc;
            //@ break_behavior requires false;
            //@ continue_behavior requires false;
            { \abstract_statement LoopBodyA; }
        }

        //@ declares \dl_localsPostProcA;
        //@ assignable \dl_localsPostProcA;
        //@ accessible \dl_heap, \dl_localsPostProcA, res, \dl_outA, \dl_localsPreProc;
        { \abstract_statement PostProcA; }
        
        //@ declares \dl_outB;
        //@ assignable \dl_outB;
        //@ accessible \nothing;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { \abstract_statement InitB; }
       
        i = -1;
        
        /*@ loop_invariant i >= -1 && i <= loopArgs.length;
          @ assignable \strictly_nothing;
          @ decreases loopArgs.length - i;
          @*/
        while (++i < loopArgs.length) {
            obj = loopArgs[i];
            
            //@ declares \dl_localsLoopBodyB;
            //@ assignable \dl_localsLoopBodyB, \dl_outB;
            //@ accessible \dl_localsLoopBodyB, obj, res, \dl_localsPreProc;
            //@ return_behavior requires false;
            //@ exceptional_behavior requires false;
            //@ break_behavior requires false;
            { \abstract_statement LoopBodyB; }
        }

        //@ declares \dl_localsPostProcB;
        //@ assignable \dl_heap, \dl_localsPostProcB;
        //@ accessible \dl_heap, \dl_localsPostProcB, res, \dl_outB, \dl_localsPreProc;
        { \abstract_statement PostProcB; }

        //@ declares \dl_localsPostProc;
        //@ assignable \dl_heap, \dl_localsPostProc, \dl_localsPreProc, \dl_outA, \dl_outB, \dl_localsPostProcA, \dl_localsPostProcB, res;
        //@ accessible \dl_heap, \dl_localsPostProc, \dl_localsPreProc, \dl_outA, \dl_outB, \dl_localsPostProcA, \dl_localsPostProcB, res;
        { \abstract_statement PostProc; }

        return res;
    }
}