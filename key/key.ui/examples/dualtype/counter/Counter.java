
class Counter {

    float value;
    int count;
    float increment;

    // ... invariants missing.

    /*@ public normal_behaviour
      @  requires 1f <= increment <= 2f;
      @  requires \fp_noerr(increment);
      @  ensures this.increment == increment;
      @  ensures this.value == 0f && \fp_noerr(this.count);
      @  ensures count == 0;
      @*/
    public Counter(float increment) {
        this.increment = increment;
    }    

    /*@ public normal_behaviour
      @  requires counter < XXX???XXX;
      @  ensures \fp_err(value) < 1e-5;
      @  assignable value, count;
      @*/
    public void increment() {
        value += increment;
        count ++;
    }
}
    
    
