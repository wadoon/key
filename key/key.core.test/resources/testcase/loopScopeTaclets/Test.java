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
    
    /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkBig(int i, boolean flag) {
        int j = i;
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = j; i > 0; i--) {if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } }
        if (flag) {i = -2;}
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = j; i > 0; i--) {if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } }
        if (flag) {i = -2;}
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = j; i > 0; i--) {if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } }
        if (flag) {i = -2;}
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = j; i > 0; i--) {if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } }
        if (flag) {i = -2;}
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = j; i > 0; i--) {if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } }
        if (flag) {i = -2;}
        
        return i;
    }
    
    /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
    public static int loopScopeRuleBenchmarkNested(int i, boolean flag) {
        int j = i;
        /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
        for (i = j; i > 0; i--) {
            if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } 
            /*@ loop_invariant
            @   i >= 0 && i <= \old(i);
            @ decreases i;
            @*/
            for (i = j; i > 0; i--) {
                if (i == 17) {i = 1;continue; } else if (i == 42) { i = -1; break; } else if (i == 2048) { i = -1; break; } 
            }
            if (flag) {i = -2;}
        }
        if (flag) {i = -2;}

        return i;
    }
}
