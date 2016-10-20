package de.tud.test.simple.loops.whileLoops;

/**
 * Simple test methods with while loops.
 *
 * @author Dominic Scheurer
 */
public class SimpleWhile {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int test(int i) {
        //@ loop_invariant true; decreases 0;
        while (i > 0) {
            i--;
        }
        
        return i;
    }
}