interface INatList {
    //@ public instance model \dl_NatList nlist;

    //@ public instance model \locset footprint;
    //@ public instance accessible \inv : footprint;

    /*@ public normal_behavior
      @ requires i != null;
      @ ensures nlist == \dl_cons(i, \old(nlist));
      // @ ensures \dl_len(nlist) == \dl_len(\old(nlist)) + 1;
      @ assignable footprint;
      */
    void cons(Nat i);
    
    /*@ public normal_behavior
      @ ensures nlist == \dl_reverse(\old(nlist));
      @ assignable footprint;
      */
    void reverse();

    /*@ public normal_behavior
      @ ensures \result == \dl_len(nlist);
      @ assignable \strictly_nothing;
      @*/
    int length();

    /*@ public normal_behavior
      @ requires i >= 0;
      @ requires i < \dl_len(nlist);
      @ ensures \result == \dl_get(nlist, i);
      @ assignable \strictly_nothing;
      @*/
    Nat get(int i);

    /*@ public normal_behavior
      @ requires \dl_len(nlist) >= 1;
      @ requires 0 <= k && k < \dl_len(nlist);
      @ ensures nlist == \dl_remove(\old(nlist), k);
      @ assignable footprint;
      @*/
    void remove(int k);

    /*@ public normal_behavior
      @ requires l != null;
      @ requires 0 <= \dl_len(l.nlist);
      @ requires \invariant_for(l);
      @ ensures nlist == \dl_append(\old(nlist), \old(l.nlist));
      @ assignable footprint;
      @*/
    void append(INatList l);
}
