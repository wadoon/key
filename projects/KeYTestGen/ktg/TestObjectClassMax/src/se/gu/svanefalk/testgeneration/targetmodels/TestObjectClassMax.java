package ObjectClassTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import se.gu.svanefalk.testgeneration.targetmodels.ObjectClass;
import se.gu.svanefalk.testgeneration.targetmodels.ClassProxy;

public  class TestObjectClassMax {
    
    @Test
    public void testmax0 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        ObjectClass self = new ObjectClass();        
        int b_instanceInt = 0;        
        int a_instanceInt = 0;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        ClassProxy a = new ClassProxy();        
        ClassProxy b = new ClassProxy();        
        
        /*
         * Configuring variable: a
         */
        setFieldValue(a,"instanceInt",0);        
        
        /*
         * Configuring variable: b
         */
        setFieldValue(b,"instanceInt",0);        
        
        ClassProxy result = self.max(a,b);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result != null;            
        );        
        
    }
    
    @Test
    public void testmax1 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        ObjectClass self = new ObjectClass();        
        int b_instanceInt = 0;        
        int a_instanceInt = 1;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        ClassProxy a = new ClassProxy();        
        ClassProxy b = new ClassProxy();        
        
        /*
         * Configuring variable: a
         */
        setFieldValue(a,"instanceInt",1);        
        
        /*
         * Configuring variable: b
         */
        setFieldValue(b,"instanceInt",0);        
        
        ClassProxy result = self.max(a,b);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result != null;            
        );        
        
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
