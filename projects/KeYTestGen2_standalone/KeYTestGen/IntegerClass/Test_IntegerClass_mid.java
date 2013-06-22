package IntegerClassTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import se.gu.svanefalk.testgeneration.targetmodels.IntegerClass;

public  class Test_IntegerClass_mid {
    
    @Test
    public void testmid0 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        IntegerClass self = new IntegerClass();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        int y = 1;        
        int z = 0;        
        
        /*
         * Configuring variable: self
         */
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y ||            
            result >= z            
        );        
        
        Assert.assertTrue(        
            result == z ||            
            result == y ||            
            result == x            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= y ||            
            result <= y ||            
            result <= z ||            
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= x            
        );        
        
    }
    
    @Test
    public void testmid1 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        IntegerClass self = new IntegerClass();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        int y = -1;        
        int z = 0;        
        
        /*
         * Configuring variable: self
         */
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y ||            
            result >= z            
        );        
        
        Assert.assertTrue(        
            result == z ||            
            result == y ||            
            result == x            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= y ||            
            result <= y ||            
            result <= z ||            
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= x            
        );        
        
    }
    
    @Test
    public void testmid2 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        IntegerClass self = new IntegerClass();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        int y = 0;        
        int z = 0;        
        
        /*
         * Configuring variable: self
         */
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y ||            
            result >= z            
        );        
        
        Assert.assertTrue(        
            result == z ||            
            result == y ||            
            result == x            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= y ||            
            result <= y ||            
            result <= z ||            
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= x            
        );        
        
    }
    
    @Test
    public void testmid3 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        IntegerClass self = new IntegerClass();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        int y = 0;        
        int z = 1;        
        
        /*
         * Configuring variable: self
         */
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y ||            
            result >= z            
        );        
        
        Assert.assertTrue(        
            result == z ||            
            result == y ||            
            result == x            
        );        
        
        Assert.assertTrue(        
            result >= x ||            
            result >= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= y ||            
            result <= y ||            
            result <= z ||            
            result <= z ||            
            result <= x            
        );        
        
        Assert.assertTrue(        
            result >= z ||            
            result >= x            
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
