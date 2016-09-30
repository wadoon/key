package de.tud.test.simple.arith;

/**
 * Simple test methods with some case distinctions and arithmetic operations.
 *
 * @author Dominic Scheurer
 */
public class SimpleArithmeticAndIf {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static int test(int i, boolean cpn) {
        i = i - 5;

        if (i == -1) {
            i = 42;
        }

        return i;
    }
}