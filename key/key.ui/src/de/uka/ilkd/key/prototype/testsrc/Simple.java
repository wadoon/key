
public class Simple {
    /*@ public invariant log != null && log.length == 100; @*/
    public int[] log = new int[100];

    /*@ public invariant n >= 0; @*/
    public int n;
  
  /*@ public normal_behavior
  @	requires log != null;
  @	ensures n == 0 && log != null;
  @*/

    public void init() {
        for (int i = 0; i < log.length; i++) {
            log[i] = 0;
        }
        n = 0;
    }

    /*@ public normal_behavior
      @	requires n < 100;
      @	ensures log[n] == x+y;
      @ assignable log.*;
      @*/
    public void logging(int x, int y) {
        if (n < 100) {
            log[n] = x + y;
        }

    }

    /*@ public normal_behavior
      @	requires x >= 0 && y >= 0 && n <100;
      @	ensures \result >=0;
      @ assignable log.*;
      @*/
    public int example(int x, int y) {


        if (log[n] == 0) {
            logging(x, y);
            return x + y;
        } else {
            return x + y;
        }

    }
    /*@ public normal_behavior
      @	requires a != null && b != null && (\forall int i; 0 <= i < a.length; a[i] != b[i]);
      @	ensures (\forall int i; 0 <= i < a.length; a[i] != b[i]) && \old(a) == \result;
      @*/

    public int[] compare(int[] a, int[] b){

        return a;
    }
}