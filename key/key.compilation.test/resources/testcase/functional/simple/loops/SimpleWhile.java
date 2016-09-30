package de.tud.test.simple.loops;

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
        while (i > 0) {
            i--;
        }
        
        return i;
    }
}