class Nat {
    
    public int i;

    public Nat(int i) {
	this.i = i;
    }

    /*@ public normal_behavior
      @ requires n != null;
      @ ensures \result == (this.i == n.i);
      @*/
    public boolean equals(Nat n) {
	return this.i == n.i;
    }
}
