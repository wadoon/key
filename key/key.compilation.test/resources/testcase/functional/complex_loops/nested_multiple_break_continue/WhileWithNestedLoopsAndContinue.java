package de.tud.test.complex_loops;

/**
 * Test case for nested loops. Should assess the transformation from
 * complex to simple loops (inner loop continues should not be transformed).
 *
 * @author Dominic Scheurer
 */
public class WhileWithNestedLoopsAndContinue {
    
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
            
            /*@ loop_invariant true; decreases 0;
              @*/
            while (true) {
                if (i > 0) {
                    // The "break" makes things more
                    // complicated in the invariant rule...
                    break;
                }
                
                continue;
            }

            if (i == 4) {
                i--;
                continue;
            }
            
            i--;
        }
        
        return i;
    }
}