public interface INatSet {
    //@ public instance model \dl_NatSet nset;

    //@ public instance model \locset footprint;
    //@ public instance accessible \inv : footprint;

    
    /*@ public normal_behavior
      @ requires true;
      @ ensures nset == \dl_set_add(\old(nset), i);
      @ ensures \new_elems_fresh(footprint);
      @ assignable footprint;
      @*/
    public void setadd(Nat i);

    /*@ public normal_behavior
      @ requires true;
      @ ensures nset == \dl_remove(\old(nset), i);
      @ assignable footprint;
      @*/
    public void remove(Nat i);

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == \dl_eqv(nset, s.nset);
      @ assignable \strictly_nothing;
      @*/
    public boolean equals(NatSetImpl s);


    /*@ public normal_behavior
      @ ensures \result == \dl_len(nset);
      @ assignable \strictly_nothing;
      @*/
    public int len();
}
