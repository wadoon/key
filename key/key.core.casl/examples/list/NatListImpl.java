public class NatListImpl implements INatList {
    //@ public instance ghost \dl_NatList impl;

    //@ represents nlist = impl;
    //@ represents footprint = a, a[*], impl;
    
    //@ invariant a != null;
    //@ invariant a.length >= 0;

    /*@ invariant (\forall int x; 0 <= x && x < a.length; \dl_get(impl, x) == a[x]);
      @ invariant (\forall int x; 0 <= x && x < a.length; a[x] != null);
      @ invariant \dl_len(impl) == a.length;
      @ invariant \dl_len(impl) >= 0;
      @*/

    /*@ public normal_behavior
      @ ensures a != null;
      @ ensures \new_elems_fresh(footprint);
      @ ensures impl == \dl_nil();
      @ ensures 0 == \dl_len(impl);
      @ ensures \fresh(footprint);
      @ assignable footprint;
      @*/
    public /*@ pure @*/  NatListImpl() {
	//@ set impl = \dl_nil();
	a = new Nat[0];
    }
    
    public /*@ nonnull @*/ Nat a[];
    //int len;

    public void cons(Nat i) {
	Nat[] a_ = new Nat[a.length+1];

	/*@ loop_invariant 1 <= idx <= a_.length;
	  // @ loop_invariant a.length >= 1;
	  @ loop_invariant a_.length == a.length + 1;
	  @ loop_invariant (\forall int k; 1 <= k < idx; a_[k] == \old(a[k - 1]));
	  @ decreases a_.length - idx;
	  @ assignable a_[1 .. a_.length];
	*/
	for (int idx = 1; idx < a_.length; idx++) {
	    a_[idx] = a[idx - 1];
	}
	//@ set impl = \dl_cons(i, impl);
	a = a_;
	a[0] = i;
    }
    
    public int length() {
	return a.length;
    }

    public Nat get(int i) {
	return a[i];
    }

    public void reverse() {
	Nat[] a_ = new Nat[a.length];
	/*@ loop_invariant 0 <= i <= a.length;
	  @ loop_invariant (\forall int l; 0 <= l < i; a_[l] == \old(a[a.length-l-1]));
	  @ decreases a.length - i;
	  @ assignable a_[*];
	  @*/
	for (int i = 0; i < a.length; i++) {
	    a_[i] = a[a.length-i-1];
	}
	//@ set impl = \dl_reverse(impl);
	a = a_;
    }


    public void remove(int k) {
	Nat[] a_ = new Nat[a.length-1];
	/*@ loop_invariant 0 <= i1 <= k;
	  @ loop_invariant (\forall int i; 0 <= i < i1; a_[i] == \old(a[i]));
	  @ loop_invariant (\forall int i; 0 <= i < i1; a_[i] != null);
	  @ decreases k - i1;
	  @ assignable a_[0 .. k - 1];
	  @*/
	for (int i1 = 0; i1 < k; i1++) {
	    a_[i1] = a[i1];
	}
	/*@ loop_invariant k <= i2 <= a_.length;
	  @ loop_invariant (\forall int i; 0 <= i < i1; a_[i] == \old(a[i]));
	  @ loop_invariant (\forall int i; i1 <= i < i2; a_[i] == \old(a[i + 1]));
	  @ loop_invariant (\forall int i; 0 <= i < i2; a_[i] != null);
	  @ decreases \old(a).length - 1 - i2;
	  @ assignable a_[k .. (\old(a).length - 1)];
	  @*/
	for (int i2 = k; i2 < a_.length; i2++) {
	    a_[i2] = a[i2 + 1];
	}	
	//@ set impl = \dl_remove(impl, k);
	a = a_;
    }

    public void append(INatList l) {
	    int newlen = length() + l.length();
	    Nat[] a_ = new Nat[newlen];
	    int i = 0;
	    /*@ loop_invariant 0 <= i <= a.length;
	      @ loop_invariant (\forall int k; 0 <= k < i; a_[k] == \old(a[k]));
	      @ loop_invariant (\forall int k; 0 <= k < i; a_[k] != null);
	      @ decreases a.length - i;
	      @ assignable a_[0 .. a.length];
	      @*/
	    for (i = 0; i < length(); i++) {
		    a_[i] = a[i];
	    }
	    /*@ loop_invariant 0 <= j <= l.length();
	      @ loop_invariant (\forall int k; 0 <= k < i; a_[k] == \old(a[k]));
	      @ loop_invariant (\forall int k; 0 <= k < i; a_[k] != null);
	      @ loop_invariant (\forall int k; 0 <= k < j; a_[i+k] == l.get(k));
	      @ loop_invariant (\forall int k; 0 <= k < j; a_[i+k] != null);
	      @ decreases l.length() - j;
	      @ assignable a_[i .. i + l.length()];
	      @*/
	    for (int j = 0; j < l.length(); j++) {
		    a_[i+j] = l.get(j);
	    }
	    //@ set impl = \dl_append(impl, l.nlist);
	    a = a_;
    }
}
