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
 * A model of the "Remove Control Flag" refactoring by M. Fowler.
 * 
 * This refactoring is surprisingly difficult, since one loop runs one time more
 * than the other. Therefore, we cannot relate the i-th run in both loops, but
 * have to relate the i-th of the one with the "true" guard to the (i+1)-st of
 * the other. We achieve this by unwinding the first loop once with a variant of
 * a technique described in [KKU17]. Furthermore, we add an intermediate version
 * of the refactored program which breaks, but still has the "done" variable. We
 * show the equivalence of the unwound with the intermediate and the
 * intermediate with the refactored program. For the second step, we strengthen
 * the invariant of the intermediate program (but do not change the program
 * itself).
 *
 * @author Dominic Steinhoefel
 */
public class RemoveControlFlag {
    //@ declares \dl_final(\dl_args);
    public Object before(int threshold, boolean condition, Object res, boolean done, int i) {
        done = false;
        i = 0;
        
        /*@ loop_invariant 
          @      i >= 0 && i <= threshold
          @ ; 
          @ decreases threshold - i;
          @*/
        while (!done && i < threshold) {
            // unwinding body of first loop once
            if (!done) {
                if (i < threshold) {
                    if (condition) {
                        //@ declares \dl_localsBody;
                        //@ assignable \dl_localsBody, \dl_hasTo(res);
                        //@ accessible \dl_localsBody, res, i, \dl_args;
                        //@ continue_behavior requires false; 
                        // NOTE: When body continues, the variant is violated and the loop does not necessarily termiante!
                        { abstract_statement Body; }
                        done = true;
                    }
                    
                    i++;
                }
            } else break;
            
            if (!done) {
                if (i < threshold) {
                    if (condition) {
                        //@ declares \dl_localsBody;
                        //@ assignable \dl_localsBody, \dl_hasTo(res);
                        //@ accessible \dl_localsBody, res, i, \dl_args;
                        //@ continue_behavior requires false;
                        { abstract_statement Body; }
                        done = true;
                    }
                
                    i++;
                }
            } else break;
            
        }
            
        return res;
    }
    
    //@ declares \dl_final(\dl_args);
    public Object between(int threshold, boolean condition, Object res, boolean done, int i) {
        done = false;
        i = 0;
        
        /*@ loop_invariant 
          @      i >= 0 && i <= threshold
          @ ; 
          @ decreases threshold - i;
          @*/
        while (!done && i < threshold) {
            if (condition) {
                //@ declares \dl_localsBody;
                //@ assignable \dl_localsBody, \dl_hasTo(res);
                //@ accessible \dl_localsBody, res, i, \dl_args;
                //@ continue_behavior requires false;
                { abstract_statement Body; }
       
                done = true;
                break;
            }
            
            i++;
        }
 
        return res;
    }
   
    // NOTE (DS, 2019-02-20): This only addes, compared to between, the additional
    //   invariant "!done" which is true (since if it's set to done, the program
    //   breaks from the loop, i.e. we don't need to show the invariant -- it holds
    //   before each new interation). The invariant is needed for the fact that both
    //   loops have the same number of iterations.
    //@ declares \dl_final(\dl_args);
    public Object betweenStrongerInv(int threshold, boolean condition, Object res, boolean done, int i) {
        done = false;
        i = 0;
        
        /*@ loop_invariant 
          @      i >= 0 && i <= threshold
          @   && !done  // <- Here's the change
          @ ; 
          @ decreases threshold - i;
          @*/
        while (!done && i < threshold) {
            if (condition) {
                //@ declares \dl_localsBody;
                //@ assignable \dl_localsBody, \dl_hasTo(res);
                //@ accessible \dl_localsBody, res, i, \dl_args;
                //@ continue_behavior requires false;
                { abstract_statement Body; }
       
                done = true;
                break;
            }
            
            i++;
        }
 
        return res;
    }
    
    //@ declares \dl_final(\dl_args);
    public Object after(int threshold, boolean condition, Object res, int i) {
        i = 0;
        
        /*@ loop_invariant 
          @      i >= 0 && i <= threshold
          @ ; 
          @ decreases threshold - i;
          @*/
        while (i < threshold) {
            if (condition) {
                //@ declares \dl_localsBody;
                //@ assignable \dl_localsBody, \dl_hasTo(res);
                //@ accessible \dl_localsBody, res, i, \dl_args;
                //@ continue_behavior requires false;
                { abstract_statement Body; }
       
                break;
            }
            
            i++;
        }
 
        return res;
    }
}