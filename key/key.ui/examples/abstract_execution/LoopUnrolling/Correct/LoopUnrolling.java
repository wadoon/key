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
 * This is a model of the unrolling technique mentioned in the "Abstract
 * Execution" paper.
 *
 * @author Dominic Steinhoefel
 */
public class LoopUnrolling {
    //@ declares \dl_final(\dl_args);
    public Object before(int threshold, Object res, int i, boolean b) {
        i = 0;
      
        //@ assignable \dl_hasTo(b);
        //@ accessible res, i, \dl_args;
        //@ return_behavior requires false;
        //@ continue_behavior requires false;
        //@ break_behavior requires false;
        { abstract_statement Guard; }
        
        /*@ loop_invariant 
          @      i >= 0 && i <= threshold
          @ ; 
          @ decreases threshold - i;
          @*/
        while (b && i < threshold) {
            //@ assignable \dl_hasTo(res);
            //@ accessible res, i, \dl_args;
            //@ continue_behavior requires false;
            { abstract_statement Body; }

            //@ assignable \dl_hasTo(b);
            //@ accessible res, i, \dl_args;
            //@ return_behavior requires false;
            //@ continue_behavior requires false;
            //@ break_behavior requires false;
            { abstract_statement Guard; }

            i++;
        }

        return res;
    }
    
    //@ declares \dl_final(\dl_args);
    public Object after(int threshold, Object res, int i, boolean b) {
        i = 0;
      
        //@ assignable \dl_hasTo(b);
        //@ accessible res, i, \dl_args;
        //@ return_behavior requires false;
        //@ continue_behavior requires false;
        //@ break_behavior requires false;
        { abstract_statement Guard; }
        
        /*@ loop_invariant 
          @      i >= 0 && i <= threshold
          @ ; 
          @ decreases threshold - i;
          @*/
        while (b && i < threshold) {
            if (b && i < threshold) {
                //@ assignable \dl_hasTo(res);
                //@ accessible res, i, \dl_args;
                //@ continue_behavior requires false;
                { abstract_statement Body; }

                //@ assignable \dl_hasTo(b);
                //@ accessible res, i, \dl_args;
                //@ return_behavior requires false;
                //@ continue_behavior requires false;
                //@ break_behavior requires false;
                { abstract_statement Guard; }

                i++;
            } else break;
            
            if (b && i < threshold) {
                //@ assignable \dl_hasTo(res);
                //@ accessible res, i, \dl_args;
                //@ continue_behavior requires false;
                { abstract_statement Body; }

                //@ assignable \dl_hasTo(b);
                //@ accessible res, i, \dl_args;
                //@ return_behavior requires false;
                //@ continue_behavior requires false;
                //@ break_behavior requires false;
                { abstract_statement Guard; }

                i++;
            } else break;
        }

        return res;
    }
}