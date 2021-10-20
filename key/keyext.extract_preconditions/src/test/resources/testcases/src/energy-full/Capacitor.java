
public final class Capacitor {

    //@ public invariant 0 <= mode && mode <= 3;
    
    /* Modes:
     * 0: uncharged
     * 1: charged
     * 2: charged
     * 3: overcharged
     * >= 4: critically overcharged
     * 
     * The invariant states that mode 4 is never reached.
     * We want to quantify for how many inputs this can be proven.
     */
    
    private /*@spec_public@*/ int mode;
    
    /*@ public normal_behavior
      @ ensures this.mode==0;
      @ assignable this.mode;
      @*/
    public Capacitor() {
        this.mode = 0;
    }
    
    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ //requires ! (addedCharge >= 1 & this.mode >= 4 + addedCharge * -1 & this.mode >= 0 &  this.mode <= 3);
      @ ensures this.mode >= \old(this.mode) + addedCharge;
      @ assignable this.mode;
      @*/
    public void addCharge(int addedCharge) {
        mode += addedCharge;
    }
    
    /*@ public normal_behavior
      @ ensures \result == this.mode;
      @ assignable \strictly_nothing;
      @*/ 
    public int getMode() {
        return mode;
    }
}
