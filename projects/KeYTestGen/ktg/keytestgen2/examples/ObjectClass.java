package se.gu.svanefalk.testgeneration.targetmodels;

public class ObjectClass {

  /*@ public normal_behavior 
    @ ensures true;
    @*/
  public ClassProxy max(ClassProxy a, ClassProxy b) {

      if (a.instanceInt > b.instanceInt) {
          return a;
      } else {
          return b;
      }
  }
}
