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
    
    //NOTE Originally, KeY did not complain if we changed the argument
    // type in the constructor to int, that is defining an assignment
    // with incompatible types. I changed the rule assignment_write_attribute_this
    // in javaRules to forbid this behavior.
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public StringContainer(String s) {
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
