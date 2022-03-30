class Test {

    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == true;
      @*/
    public boolean test_empty_sets() {
	INatSet s1 = new NatSetImpl();
	INatSet s2 = new NatSetImpl();
	return s1.equals(s2);
    }
}
