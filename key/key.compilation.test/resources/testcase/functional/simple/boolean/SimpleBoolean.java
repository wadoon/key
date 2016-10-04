package de.tud.test.simple.bool;

public class SimpleBoolean {
    
  /*@ public normal_behavior
    @ requires true;
    @ ensures true;
    @*/
  public static boolean test(boolean b1, boolean b2) {
      boolean b3 = b1 && !b2;
      boolean b4 = b1 ^ b3;
      
      return b4;
  }
  
}
