package de.tud.test.methods;

/**
 * Some experiments with method calls to methods with non-primitive result
 * and argument types
 *
 * @author Dominic Scheurer
 */
public class NonPrimitiveMethods {
    private StringContainer s;
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public NonPrimitiveMethods(StringContainer s) {
        //TODO: Currently, we have to do an explicit super() call.
        // This should be done by the compiler if we omit it.
        super();
        
        this.s = s;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(Object o) {
        if (!(o instanceof NonPrimitiveMethods)) {
            return false;
        }
        
        return equals((NonPrimitiveMethods) o);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(NonPrimitiveMethods o) {
        return s.equals(o.s);
    }
    
    //TODO We don't get an error by the compiler so far
    // if we replace the argument type by, e.g., int. This
    // should not result in a seemingly successful compilation.
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void set(StringContainer s) {
        this.s = s;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public StringContainer get() {
        return s;
    }
  
}

class StringContainer {
    private String s;
    
    //TODO Also here, compilation finishes without an error if we
    // type "int" instead of "String" for the argument type. Have
    // to extract an error information from the proof.
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public StringContainer(String s) {
        //TODO: Currently, we have to do an explicit super() call.
        // This should be done by the compiler if we omit it.
        super();
        
        this.s = s;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(StringContainer o) {
        return s.equals(o.s);
    }
    
}
