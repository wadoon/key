package SimpleTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import Simple;

public  class TestSimpleMagic {
    
    @Test
    public void testmagic0 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        Simple self = new Simple();        
        int self_h = 0;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"h",0);        
        
        self.magic();        
        
        /*
         * Test oracle
         */
    }
    
    @Test
    public void testmagic1 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        Simple self = new Simple();        
        int self_h = 2;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"h",2);        
        
        self.magic();        
        
        /*
         * Test oracle
         */
    }
    
    /**
     * Sets a field of some object to a given value
     */
    private void setFieldValue (Object instance, String fieldName, Object value)
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        Field field = instance.getClass().getDeclaredField(fieldName);        
        field.setAccessible(true);        
        field.set(instance, value );        
    }
    
    /**
     * Gets the field of a given object
     */
    private <T> T getFieldValue (Object instance, String fieldName)
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        Field field = instance.getClass().getDeclaredField(fieldName);        
        field.setAccessible(true);        
        return (T)field.get(instance);        
    }
}
