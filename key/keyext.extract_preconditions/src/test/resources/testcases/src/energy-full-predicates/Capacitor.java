
public final class Capacitor {
    
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
      @ assignable this.*;
      @*/
    public Capacitor() {
        this.mode = 0;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (this.mode >= 0&this.mode <= 3);
      @ ensures !((this.mode>=0) & this.mode <=3);
      @*/
    public void addChargeMode11(int addedCharge) {
        mode += addedCharge;
    }
    
    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (this.mode >= 0&this.mode <= 3);
      @ ensures !(!(this.mode>=0) & this.mode <=3);
      @*/
    public void addChargeMode12(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (this.mode >= 0&this.mode <= 3);
      @ ensures !((this.mode>=0) & !(this.mode <=3));
      @*/
    public void addChargeMode13(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (this.mode >= 0&this.mode <= 3);
      @ ensures !(!(this.mode>=0) & !(this.mode <=3));
      @*/
    public void addChargeMode14(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & this.mode <=3);
      @ ensures !(this.mode >= 0&this.mode <= 3);
      @*/
    public void addChargeMode21(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & this.mode <=3);
      @ ensures !(!(this.mode>=0) & this.mode <=3);
      @*/
    public void addChargeMode22(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & this.mode <=3);
      @ ensures !((this.mode>=0) & !(this.mode <=3));
      @*/
    public void addChargeMode23(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & this.mode <=3);
      @ ensures !(!(this.mode>=0) & !(this.mode <=3));
      @*/
    public void addChargeMode24(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires ((this.mode>=0) & !(this.mode <=3));
      @ ensures !(this.mode >= 0&this.mode <= 3);
      @*/
    public void addChargeMode31(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires ((this.mode>=0) & !(this.mode <=3));
      @ ensures !(!(this.mode >= 0)&(this.mode <= 3));
      @*/
    public void addChargeMode32(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires ((this.mode>=0) & !(this.mode <=3));
      @ ensures !((this.mode >= 0)&!(this.mode <= 3));
      @*/
    public void addChargeMode33(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires ((this.mode>=0) & !(this.mode <=3));
      @ ensures !(!(this.mode >= 0)&!(this.mode <= 3));
      @*/
    public void addChargeMode34(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & !(this.mode <=3));
      @ ensures !((this.mode >= 0)&(this.mode <= 3));
      @*/
    public void addChargeMode41(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & !(this.mode <=3));
      @ ensures !(!(this.mode >= 0)&(this.mode <= 3));
      @*/
    public void addChargeMode42(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & !(this.mode <=3));
      @ ensures !((this.mode >= 0)&!(this.mode <= 3));
      @*/
    public void addChargeMode43(int addedCharge) {
        mode += addedCharge;
    }

    /*@ public normal_behavior
      @ requires addedCharge >= 0;
      @ requires (!(this.mode>=0) & !(this.mode <=3));
      @ ensures !(!(this.mode >= 0)&!(this.mode <= 3));
      @*/
    public void addChargeMode44(int addedCharge) {
        mode += addedCharge;
    }



}
