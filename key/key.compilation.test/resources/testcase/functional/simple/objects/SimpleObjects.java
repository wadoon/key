package de.tud.test.simple.objects;

public class SimpleObjects {
    
  /*@ public normal_behavior
    @ requires true;
    @ ensures true;
    @*/
  public static boolean identical(Object o1, Object o2) {
      return o1 == o2;
  }
    
  /*@ public normal_behavior
    @ requires true;
    @ ensures true;
    @*/
//  public static boolean equals(Object o1, Object o2) {
//      return o1.equals(o2);
//  }
  
}
