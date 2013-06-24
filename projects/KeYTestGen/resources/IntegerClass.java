package se.gu.svanefalk.testgeneration.targetmodels;

public class IntegerClass {

    /*@ public normal_behavior
      @ ensures (\result == x) || (\result == y) || (\result == z );
      @ ensures ((\result <= y) && (\result <= z )) || ((\result <= y) &&
          (\result <= x )) || ((\result <= x) && (\result <= z ));
      @ ensures ((\result >= y) && (\result >= z )) || ((\result >= y) &&
         (\result >= x )) || ((\result >= x) && (\result >= z ));
      @*/
    public static int mid(final int x, final int y, final int z) {

        int mid = z;
        if (y < z) {
            if (x < y) {
                mid = y;
            } else if (x <= z) {
                mid = x;
            }
        } else {
            if (x > y) {
                mid = y;
            } else if (x >= z) {
                mid = x;
            }
        }
        return mid;
    }
    
    /*@ public normal_behavior 
    @ ensures true;
    @*/
  public int max(int a, int b) {

      if (a > b) {
          return a;
      } else {
          return b;
      }
  }

  /*@ public normal_behavior 
    @ ensures true;
    @*/
  public int min(int a, int b) {

      if (a < b) {
          return a;
      } else {
          return b;
      }
  }
}
