package IntegerClassTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import se.gu.svanefalk.testgeneration.targetmodels.IntegerClass;

public  class Test_IntegerClass_min {
    
    @Test
    public void testmin0 ()
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
        int b = 1;        
        
        /*
         * Configuring variable: self
         */
        int result = self.min(a,b);        
        
        /*
         * Test oracle
         */
    }
    
    @Test
    public void testmin1 ()
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
        int b = 1;        
        
        /*
         * Configuring variable: self
         */
        int result = self.min(a,b);        
        
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
