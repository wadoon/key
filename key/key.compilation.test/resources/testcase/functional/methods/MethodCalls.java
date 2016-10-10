package de.tud.test.methods;

/**
 * Some experiments with method calls.
 *
 * @author Dominic Scheurer
 */
public class MethodCalls {
    private int i;
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public MethodCalls(int i) {
        //TODO: Currently, we have to do an explicit super() call.
        // This should be done by the compiler if we omit it.
        super();
        
        this.i = i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(Object o) {
        if (!(o instanceof MethodCalls)) {
            return false;
        }
        
        return equals((MethodCalls) o);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals2(Object o) {
        if (!(o instanceof MethodCalls)) {
            return false;
        }
        
        return ((MethodCalls) o).equals(this);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(MethodCalls o) {
        return i == o.i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void set(int i) {
        this.i = i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void set2(int i) {
        set(this, i);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static void set(MethodCalls o, int i) {
        o.i = i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public int get() {
        return i;
    }
  
}
