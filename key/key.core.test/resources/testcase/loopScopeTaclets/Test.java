public class TestNoLabels {
    /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkWhileNoLabels(int i, boolean flag) {
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
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
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkTwoForNoLabels(int i, boolean flag) {
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
    
//    k = 0;
//    /*@ loop_invariant
//    @ k == (x-i)*x && i <= x && i >= n;
//    @ decreases i;
//    @*/
//    for (i = x; i > n; i--) {
//        k += x;
//    }
    
//    k = 0; /*@ loop_invariant @ k == (x-i)*x && i <= x && i >= n; @ decreases i; @*/ for (i = x; i > n; i--) { k += x; }
    
    /*@ public normal_behavior
    @ requires n >= 0 && i >= n;
    @ ensures (\result == (\old(i)-n)*\old(i));
    @*/
    public static int loopScopeRuleBenchmarkForBig(int i, int n) {
        int x = i;
        int k;
        
        // 10
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        
     // 10
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        
     // 10
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        
     // 10
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        k = 0;
        /*@ loop_invariant
        @ k == (x-i)*x && i <= x && i >= n;
        @ decreases i;
        @*/
        for (i = x; i > n; i--) { k += x; }
        
        return k;
    }
    
    /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkNested(int i, boolean flag) {
        int x = i;
        
        /*@ loop_invariant
        @   i >= -1 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = x; i > 0; i--) {
            if (i == 17) {i = 1; continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } 
            
            /*@ loop_invariant
            @   j >= 0 && i <= \old(j);
            @ decreases j;
            @*/
            for (int j = i; j > 0; j--) {
                if (j == 17) {i = 1; continue; } else if (j == 42) { i = -1; break; } else if (j == 2048) { i = -1; break; } 
            }
        }
        if (flag) {i = -2;}

        return i;
    }
}
