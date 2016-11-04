package de.tud.test.complex_loops;

/**
 * Test case for a while loop with one break. Breaks make things compilicated in
 * the invariant rule, therefore this test case is created for testing it quite
 * in isolation.
 *
 * @author Dominic Scheurer
 */
public class WhileWithOneBreak {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int testSimpleBreak(int i) {
        //@ loop_invariant true; decreases 0;
        while (i > 0) {
            if (i == 3) {
                i = 0;
                break;
            }
            
            i--;
        }
        
        return i;
    }
    
}