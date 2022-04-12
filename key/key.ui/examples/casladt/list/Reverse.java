final class Reverse {

    final Nat nat1 = new Nat(1);
    final Nat nat2 = new Nat(2);
    final Nat nat3 = new Nat(3);
    final Nat nat4 = new Nat(4);

    /*@ public normal_behavior
      @ ensures \result.nlist == \dl_cons(nat3, \dl_cons(nat2, \dl_cons(nat1, \dl_nil())));
      @ ensures \dl_len(\result.nlist) == 3;
      @ ensures \fresh(\result);
      @*/
    public INatList test() {
        final INatList nl = new NatListImpl();
        nl.cons(nat3);
        nl.cons(nat2);
        nl.cons(nat1);
        nl.reverse();
        return nl;
    }

    /*@ public normal_behavior
      @ ensures \result.nlist == \dl_cons(nat2, \dl_cons(nat3, \dl_nil()));
      @ ensures \dl_len(\result.nlist) == 2;
      @*/
    public INatList test_remove() {
        final INatList nl = new NatListImpl();
        nl.cons(nat3);
        nl.cons(nat2);
        nl.cons(nat1);
        nl.remove(0);
        return nl;
    }
}
