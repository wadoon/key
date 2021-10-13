class Bubblesort {


    /*@ public normal_behaviour
      @  requires (\forall int i; 0 <= i < a.length; a[i] >= 0);
      @  ensures (\forall int i; 0 <= i < a.length-1; a[i] <= a[i+1]);
      @  ensures \dl_seqPerm(\old(\dl_array2seq(a)), \dl_array2seq(a));
      @  assignable a[*];
      @*/
    public static void sort(int a[]) {
        boolean sorted = false;

        /*@ loop_invariant \dl_seqPerm(\old(\dl_array2seq(a)), \dl_array2seq(a));
	  @ loop_invariant (\forall int i; 0 <= i < a.length; a[i] >= 0);
          @ loop_invariant sorted ==> (\forall int i; 0 <= i < a.length-1; a[i] <= a[i+1]);
          @ decreases (sorted?0:1), \dl_array2seq(a);
          @ assignable a[*];
          @*/
        while(!sorted) {
            sorted = true;
            //@ ghost \seq last = \dl_array2seq(a);
            //@ ghost int diff;
            
            /*@ loop_invariant 0 <= j < a.length || j == 0;
	      @ loop_invariant (\forall int i; 0 <= i < a.length; a[i] >= 0);
              @ loop_invariant sorted ==>
              @  (\forall int i; 0 <= i < j; a[i] <= a[i+1]);
              @ loop_invariant sorted ==> \dl_array2seq(a) == last;
              @ loop_invariant !sorted ==> a[diff] < (int)last[diff] && 0 <= diff < j &&
              @   (\forall int l; 0 <= l < diff; a[l] == (int)last[l]);
              @ loop_invariant \dl_seqPerm(\old(\dl_array2seq(a)), \dl_array2seq(a));
              @ decreases a.length - j;
              @ assignable a[*];
              @*/
            for(int j = 0; j < a.length-1; j++) {
                if (a[j] > a[j+1]) {
                    int t = a[j];
                    a[j] = a[j+1];
                    a[j+1] = t;
                    if(sorted) {
                        //@ set diff = j;
                    }
                    sorted = false;
                }
            }
        }
    }
}
