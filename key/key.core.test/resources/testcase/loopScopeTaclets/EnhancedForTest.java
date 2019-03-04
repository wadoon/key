class For {

  int[] a;
  For f;

  //@ ensures \result == (\sum int j; 0 <= j && j < a.length; a[j]);
  int sum (int i) {
    int s = 0;
    int z = a.length;

    /*@ maintaining s == (\sum int j; 0 <= j && j < i; a[j]);
      @ maintaining 0 <= i && i <= a.length;
      @ decreasing a.length - i;
      @ assignable \strictly_nothing;
      @*/
    for (i = 0; i < a.length; i++) s+= a[i];
    return s;
  }

  /*@ requires \invariant_for(f);
    @ diverges true;
    @ ensures false;
    @*/
  void infiniteLoop() {
    //@ maintaining \invariant_for(f);
    //@ assignable \strictly_nothing;
    for (Object o: f);
  }
}
