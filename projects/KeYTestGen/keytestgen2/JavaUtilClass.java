package se.gu.svanefalk.testgeneration.targetmodels;

import java.util.LinkedList;

public class JavaUtilClass {

  /*@ public normal_behavior 
    @ ensures true;
    @*/
  public int max(int a, int b) {
      LinkedList list = new LinkedList();
      if (list.isEmpty()) {
          return a;
      } else {
          return b;
      }
  }
}
