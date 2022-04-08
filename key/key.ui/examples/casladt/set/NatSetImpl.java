public class NatSetImpl implements INatSet {
    //@ public instance ghost \dl_NatSet impl;

    //@ represents nset = impl;

    //@ invariant (\forall int x; 0 <= x && x < a.length; \dl_set_contains(impl, a[x]));
    //@ invariant (\forall int x; 0 <= x && x < a.length; a[x] != null);
    
    //@ represents footprint = a, a[*];
    //@ invariant a.length >= 0;

    public Nat a[];
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures a != null;
      @ ensures \new_elems_fresh(footprint);
      @ ensures nset == \dl_tip();
      @ assignable footprint;
      @*/
    public NatSetImpl() {
	//@ set impl = \dl_tip();
	this.a = new Nat[0];
    }

    /*@ public normal_behavior
      @ requires n != null;
      @ ensures \dl_set_contains(impl, n);
      @*/
    boolean contains(Nat n) {
	/*@ loop_invariant 0 <= i <= a.length;
	  @ loop_invariant (\forall int j; 0 <= j < i; a[j] != n);
	  @ decreases a.length - i;
	  @ assignable \strictly_nothing;
	  @*/
	for (int i = 0; i < a.length; i++) {
	    if (n == a[i]) {
		return true;
	    }
	}
	return false;
    }

    /*@ public normal_behavior
      @ requires other != null;
      @*/
    public boolean subset(NatSetImpl other) {
	for (int i = 0; i < this.a.length; i++) {
	    if (!other.contains(this.a[i]))
		return false;
	}
	return true;
    }

    public boolean equals(NatSetImpl s) {
	return this.subset(s) && s.subset(this);
    }

    public void setadd(Nat n) {
	Nat[] a_ = new Nat[a.length+1];
	/*@ loop_invariant 0 <= i <= a.length;
	  @ loop_invariant (\forall int i; 0 <= i < a.length; a_[i] == \old(a[i]));
	  @ decreases a.length - i;
	  @ assignable a_[0 .. a.length];
	  @*/
	for (int i = 0; i < a.length; i++) {
	    a_[i] = a[i];
	}
	a_[a.length] = n;
	//@ set impl = \dl_set_add(impl, n);
	a = a_;
    }
}
