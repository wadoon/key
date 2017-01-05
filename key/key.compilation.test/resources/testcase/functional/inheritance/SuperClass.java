package de.tud.test.inheritance;

//XXX Making this class abstract leads to the phenomenon that 
// for instance #equals(Object) is not executed, but the proof
// tree closed because of an unsatisfiable assumption...
// The unsatisfiable assumption is
// de.tud.test.inheritance.SuperClass::exactInstance(self) = TRUE
// But it might happen that equals is not overridden, and actually
// used by subclasses!
public /*abstract*/ class SuperClass {
    protected NatWrapper nat;
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    private SuperClass() {
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    protected SuperClass(NatWrapper nat) {
        this(); // Optional
        this.nat = nat;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(Object o) {
        return false;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    protected static Object zeroInstance() {
        return new NatWrapper(0);
    }
    
}

class NatWrapper {
    private int i;
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public NatWrapper(int i) {
        this.i = i < 0 ? -i : i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public int get() {
        return i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public String toString() {
        return i+"";
    }
}