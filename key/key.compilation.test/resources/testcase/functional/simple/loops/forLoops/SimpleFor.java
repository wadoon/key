package de.tud.test.simple.loops.forLoops;

/**
 * Simple test methods with for loops.
 *
 * @author Dominic Scheurer
 */
public class SimpleFor {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int test(int i) {
        for (int j = 0; j < 4; j++) {
            i += j;
        }
        
        return i;
    }
}