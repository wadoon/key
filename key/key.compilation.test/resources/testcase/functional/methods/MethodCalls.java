package de.tud.test.simple.objects;

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
    public boolean equals(MethodCalls o) {
        return i == o.i;
    }
  
}
