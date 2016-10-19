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
      @ diverges true;
      @*/
    public static int test(int i) {
        /*@ loop_invariant true;
          @*/
        while (i > 0) {
            if (i == 3) {
                i--;
                continue;
            }
            
            /*@ loop_invariant true;
              @*/
            while (true) {
                if (i > 0) {
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