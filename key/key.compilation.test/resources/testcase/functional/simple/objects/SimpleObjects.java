package de.tud.test.simple.objects;

/**
 * Demonstrates some simple object-oriented features: Identity on objects,
 * construction of objects with parameters, and field access.
 *
 * @author Dominic Scheurer
 */
public class SimpleObjects {
    private int i;
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public SimpleObjects(int i) {
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
        if (!(o instanceof SimpleObjects)) {
            return false;
        }
        
        return i == ((SimpleObjects) o).i;
        
        //TODO: Also support method calls. Maybe have to implement
        //a special taclet for doing this, as in the case of loops...
        // return equals((SimpleObjects) o);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(SimpleObjects o) {
        return i == o.i;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public static boolean identical(Object o1, Object o2) {
        return o1 == o2;
    }
  
}
