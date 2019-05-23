public class DutchFlag {
    private static int wb;
    private static int wt;
    private static int bb;

    /*@ public normal_behavior
      @ requires   A.length > 0
      @            && (\forall int i; i>=0 & i<A.length; A[i] == 0 || A[i] == 1 || A[i] == 2);
      @ ensures    (\forall int q; q >= 0 && q < wb; \result[q]==0)
      @         && (\forall int q; q >= wb && q < wt; \result[q]==1)
      @         && (\forall int q; q >= bb && q < \result.length; \result[q]==2)
      @         && 0<=wb && wb<=wt && wt==bb && bb<=A.length;
      @*/
    public static int[] dutchFlagStep0(int[] A) {
        /*@ declares \dl_localsP0;
          @ assignable \dl_localsP0, wb, wt, bb, A[*];
          @ accessible \dl_localsP0, wb, wt, bb, A[*];
          @
          @ normal_behavior
          @ ensures    (\forall int q; q >= 0 && q < wb; A[q]==0)
          @         && (\forall int q; q >= wb && q < wt; A[q]==1)
          @         && (\forall int q; q >= bb && q < A.length; A[q]==2)
          @         && 0<=wb && wb<=wt && wt==bb && bb<=\old(A.length);
          @
          @ exceptional_behavior requires false;
          @ return_behavior requires false;
          @*/
        { \abstract_statement P0; }
        
        return A;
    }

    /*@ public normal_behavior
      @ requires   A.length > 0
      @            && (\forall int i; i>=0 & i<A.length; A[i] == 0 || A[i] == 1 || A[i] == 2);
      @ ensures    (\forall int q; q >= 0 && q < wb; \result[q]==0)
      @         && (\forall int q; q >= wb && q < wt; \result[q]==1)
      @         && (\forall int q; q >= bb && q < \result.length; \result[q]==2)
      @         && 0<=wb && wb<=wt && wt==bb && bb<=A.length;
      @*/
    public static int[] dutchFlagConcrete(int[] A) {
        wb = 0;
        wt = 0;
        bb = A.length;
        
        /*@ loop_invariant    (\forall int i; i>=0 & i<A.length; A[i] == 0 || A[i] == 1 || A[i] == 2)
                           && (\forall int q; q >= 0 && q < wb; A[q]==0)
                           && (\forall int q; q >= wb && q < wt; A[q]==1)
                           && (\forall int q; q >= bb && q < A.length; A[q]==2)
                           && 0<=wb && wb<=wt && wt<=bb && bb<=A.length;
            decreases bb - wt; @*/
        while (wt != bb) {
            if (A[wt] == 0) {
                int t = A[wt];
                A[wt] = A[wb];
                A[wb] = t;
                wt = wt + 1;
                wb = wb + 1;
            } else if (A[wt] == 1) {
                wt = wt + 1;
            } else if (A[wt] == 2) {
                int t = A[wt];
                A[wt] = A[bb - 1];
                A[bb - 1] = t;
                bb = bb - 1;
            }
        }
        
        return A;
    }
}