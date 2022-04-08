class Nat {
    
    public int i;

    public Nat(int i) {
	this.i = i;
    }

    public boolean equals(Nat n) {
	return this.i == n.i;
    }

    // /*@ requires b != null;
    // @ ensures (\forall int x; 0 <= x < b.length; \result[\result.length-x-1] == \old(b[x]));
    // @*/
    // Nat[] reverse_int(Nat[] b) {
    // 	Nat[] a_ = new Nat[b.length];
    // 	/*@ loop_invariant 0 <= i && i <= b.length;
    // 	  @ loop_invariant (\forall int x; 0 <= x < i; a_[x] == b[b.length-x-1]);
    // 	  @ decreases b.length - i;
    // 	  @ assignable a_[*];
    // 	  @*/
    // 	for (int i = 0; i < b.length; i++) {
    // 	    a_[i] = b[b.length - i - 1];
    // 	}
    // 	return a_;
    // }

    // /*@ requires is != null;
    // @ ensures \fresh(\result);
    // @*/
    // int[] cons(int i, int[] is) {
    // 	int[] is_ = new int[is.length + 1];
    // 	is_[0] = i;
    // 	/*@ loop_invariant 1 <= idx <= is_.length;
    // 	  @ loop_invariant (\forall int x; 1 <= x < idx; is_[idx] == is[idx-1]);
    // 	  @ decreases is_.length - idx;
    // 	  @ assignable is_[1 .. is_.length];
    // 	  @*/
    // 	for (int idx = 1; idx < is_.length; idx++) {
    // 	    is_[idx] = is[idx-1];
    // 	}
    // 	return is_;
    // }
}
