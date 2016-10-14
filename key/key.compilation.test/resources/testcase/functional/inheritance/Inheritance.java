package de.tud.test.inheritance;

/**
 * Some experiments with inheritance.
 * 
 * TODO: Test access to non-constructor super methods.
 *
 * @author Dominic Scheurer
 */
public class Inheritance extends SuperClass {
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public Inheritance(int i) {
        //XXX We can not write "super(new NatWrapper(i));", because then
        // SE does not finish...
        super(null);
        nat = new NatWrapper(i);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public void set(int i) {
        //XXX KeY does not support "super.nat"; we have to
        // write "nat", although it's a field in the super
        // class of this class.
        nat = new NatWrapper(i);
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public NatWrapper get() {
        return nat;
    }
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures true;
      @*/
    public boolean equals(Object o) {
        if (nat.get() == 17) {
            // This is a deliberate and very obvious bug ;)
            return super.equals(o);
        }
        
        return (o instanceof Inheritance)
                && ((Inheritance) o).nat.get() == nat.get();
    }
    
}
