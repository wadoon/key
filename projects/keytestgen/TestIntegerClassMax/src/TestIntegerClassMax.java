package IntegerClassTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import IntegerClass;

public  class TestIntegerClassMax {
    
    @Test
    public void testmax0 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        IntegerClass self = new IntegerClass();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int a = 0;        
        int b = 0;        
        
        int result = self.max(a,b);        
        
        /*
         * Test oracle
         */
    }
    
    @Test
    public void testmax1 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        IntegerClass self = new IntegerClass();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int a = 1;        
        int b = 0;        
        
        int result = self.max(a,b);        
        
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
