public class TestNoLabels {
    /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkWhileNoLabels(int i, boolean flag) {
        
        while (i > 0) {
            if (i == 17) {
                i = 0;
                continue; // have to prove the invariant
            }
            else if (i == 42) {
                i = -1;
                break; // have to prove the postcondition!
            }
            else if (i == 2048) {
                i = -1;
                break; // have to prove the postcondition!
            }

            i--;
        }

        if (flag) {
            i = -2;
        }

        return i;
    }
    
    /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkForNoLabels(int i, boolean flag) {
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = i; i > 0; i--) {
            if (i == 17) {
                i = 1;
                continue; // have to prove the invariant
            }
            else if (i == 42) {
                i = -1;
                break; // have to prove the postcondition!
            }
            else if (i == 2048) {
                i = -1;
                break; // have to prove the postcondition!
            }
        }

        if (flag) {
            i = -2;
        }

        return i;
    }
    
    /*@ public normal_behavior
    @ ensures true;
    @*/
  public static void benchmarkWhile() {
      int j;

      // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
      // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
   // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
      // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
   // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
      // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
   // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      
      // 5
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
      j = 0;
      //@ loop_invariant j >= 0 && j <= 15;
      //@ decreases 15 - j;
      while (j < 15) {j=j+1;}
  }
    
    /*@ public normal_behavior
      @ ensures true;
      @*/
    public static void benchmarkFor() {
        int j;

        // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
        // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
        // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
        // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
     // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
        // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
     // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        
        // 5
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
        j = 0;
        //@ loop_invariant j >= 0 && j <= 15;
        //@ decreases 15 - j;
        for (; j < 15; j=j+1) {}
    }
}
