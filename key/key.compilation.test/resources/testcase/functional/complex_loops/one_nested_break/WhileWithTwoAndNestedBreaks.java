package de.tud.test.complex_loops;

/**
 * Test case for a while loop with one break. Breaks make things compilicated in
 * the invariant rule, therefore this test case is created for testing it quite
 * in isolation.
 *
 * @author Dominic Scheurer
 */
public class WhileWithTwoAndNestedBreaks {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int testNestedLoopComplexBreak(int i) {
        //@ loop_invariant true; decreases 0;
        while (i > 0) {
            if (i == 3) {
                //@ loop_invariant true; decreases 0;
                while (i > 0) {
                    i = 0;
                    break;
                }
                break;
            }
            
            i--;
        }
        
        return i;
    }
}