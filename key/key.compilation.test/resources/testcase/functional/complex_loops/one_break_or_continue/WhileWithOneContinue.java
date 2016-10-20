package de.tud.test.complex_loops;

/**
 * Test case for a while loop with one continue. Should assess the
 * transformation from complex to simple loops (inner loop continues should not
 * be transformed).
 *
 * @author Dominic Scheurer
 */
public class WhileWithOneContinue {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int test(int i) {
        /*@ loop_invariant true; decreases 0;
          @*/
        while (i > 0) {
            if (i == 3) {
                i--;
                continue;
            }
            
            i--;
        }
        
        return i;
    }
}