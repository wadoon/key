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
    public static int[] dutchFlagStep1(int[] A) {
        wb = 0;
        wt = 0;
        bb = A.length;
        
        /*@ declares \dl_localsP1;
          @ assignable \dl_localsP1, wb, wt, bb, A[*];
          @ accessible \dl_localsP1, wb, wt, bb, A[*];
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
        { \abstract_statement P1; }
        
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
    public static int[] dutchFlagStep2(int[] A) {
        wb = 0;
        wt = 0;
        bb = A.length;
        
        /*@ loop_invariant    (\forall int i; i>=0 & i<A.length; A[i] == 0 || A[i] == 1 || A[i] == 2)
          @                && (\forall int q; q >= 0 && q < wb; A[q]==0)
          @                && (\forall int q; q >= wb && q < wt; A[q]==1)
          @                && (\forall int q; q >= bb && q < A.length; A[q]==2)
          @                && 0<=wb && wb<=wt && wt<=bb && bb<=A.length;
          @ decreases bb - wt; @*/
        while (wt != bb) {
            //@ ghost int oldWt = wt;
            //@ ghost int oldBb = bb;
            
            /*@ declares \dl_localsP2;
              @ assignable \dl_localsP2, wb, wt, bb, A[*];
              @ accessible \dl_localsP2, wb, wt, bb, A[*];
              @
              @ normal_behavior
              @ ensures    (\forall int i; i>=0 & i<A.length; A[i] == 0 || A[i] == 1 || A[i] == 2)
              @          && (\forall int q; q >= 0 && q < wb; A[q]==0)
              @          && (\forall int q; q >= wb && q < wt; A[q]==1)
              @          && (\forall int q; q >= bb && q < A.length; A[q]==2)
              @          && 0<=wb && wb<=wt && wt<=bb && bb<=A.length
              @          && bb - wt < oldBb - oldWt;
              @
              @ exceptional_behavior requires false;
              @ return_behavior requires false;
              @ continue_behavior requires false;
              @ break_behavior requires false;
              @*/
            { \abstract_statement P2; }
        }
        
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
    public static int[] dutchFlagStep3(int[] A) {
        wb = 0;
        wt = 0;
        bb = A.length;
        
        /*@ loop_invariant    (\forall int i; i>=0 & i<A.length; A[i] == 0 || A[i] == 1 || A[i] == 2)
          @                && (\forall int q; q >= 0 && q < wb; A[q]==0)
          @                && (\forall int q; q >= wb && q < wt; A[q]==1)
          @                && (\forall int q; q >= bb && q < A.length; A[q]==2)
          @                && 0<=wb && wb<=wt && wt<=bb && bb<=A.length;
          @ decreases bb - wt; @*/
        while (wt != bb) {
            //@ ghost int oldWt = wt;
            //@ ghost int oldWb = wt;
            //@ ghost int oldBb = bb;
            //@ ghost int[] oldA = A;

            if (A[wt] == 0) {
                /*@ declares \dl_localsP3;
                  @ assignable \dl_localsP3, wb, wt, A[*];
                  @ accessible \dl_localsP3, wb, wt, A[*];
                  @
                  @ normal_behavior
                  @ ensures    A[oldWb] == oldA[oldWt] && A[oldWt] == oldA[oldWb]
                  @         && wt == oldWt + 1 && wb == oldWb + 1;
                  @
                  @ exceptional_behavior requires false;
                  @ return_behavior requires false;
                  @ continue_behavior requires false;
                  @ break_behavior requires false;
                  @*/
                { \abstract_statement P3; }
            } else if (A[wt] == 1) {
                /*@ assignable wt;
                  @ accessible wt;
                  @
                  @ normal_behavior ensures wt == oldWt + 1;
                  @
                  @ exceptional_behavior requires false;
                  @ return_behavior requires false;
                  @ continue_behavior requires false;
                  @ break_behavior requires false;
                  @*/
                { \abstract_statement P4; }
            } else if (A[wt] == 2) {
                /*@ declares \dl_localsP5;
                  @ assignable \dl_localsP5, bb, A[*];
                  @ accessible \dl_localsP5, wt, bb, A[*];
                  @
                  @ normal_behavior
                  @ ensures    A[oldBb - 1] == oldA[oldWt] && A[oldWt] == oldA[oldBb - 1]
                  @         && bb == oldBb - 1;
                  @
                  @ exceptional_behavior requires false;
                  @ return_behavior requires false;
                  @ continue_behavior requires false;
                  @ break_behavior requires false;
                  @*/
                { \abstract_statement P5; }
            }
        }
        
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
          @                && (\forall int q; q >= 0 && q < wb; A[q]==0)
          @                && (\forall int q; q >= wb && q < wt; A[q]==1)
          @                && (\forall int q; q >= bb && q < A.length; A[q]==2)
          @                && 0<=wb && wb<=wt && wt<=bb && bb<=A.length;
          @ decreases bb - wt; @*/
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