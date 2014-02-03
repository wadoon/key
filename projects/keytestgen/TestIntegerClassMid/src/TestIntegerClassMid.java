package IntegerClassTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import IntegerClass;

public  class TestIntegerClassMid {
    
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
        int z = 2;        
        
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= y ||            
            result <= x ||            
            result <= z ||            
            result <= z ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
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
            result >= z ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= z            
        );        
        
        Assert.assertTrue(        
            result >= y ||            
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
        int y = 0;        
        int z = 1;        
        
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= y ||            
            result <= x ||            
            result <= z ||            
            result <= z ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
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
            result >= z ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= z            
        );        
        
        Assert.assertTrue(        
            result >= y ||            
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
        int x = 1;        
        int y = 0;        
        int z = 0;        
        
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= y ||            
            result <= x ||            
            result <= z ||            
            result <= z ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
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
            result >= z ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= z            
        );        
        
        Assert.assertTrue(        
            result >= y ||            
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
        int z = 0;        
        
        int result = self.mid(x,y,z);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result <= y ||            
            result <= x ||            
            result <= z ||            
            result <= z ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= y            
        );        
        
        Assert.assertTrue(        
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
            result >= z ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= z            
        );        
        
        Assert.assertTrue(        
            result >= y ||            
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
