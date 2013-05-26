import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import se.gu.svanefalk.testgeneration.targetmodels.ClassProxy;
import se.gu.svanefalk.testgeneration.targetmodels.PrimitiveIntegerOperations;

public  class Test_PrimitiveIntegerOperations_midOneProxyOneInstance {
    
    @Test
    public void testmidOneProxyOneInstance0 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();        
        ClassProxy self_proxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy = new ClassProxy();        
        int instanceInt = 0;        
        ClassProxy nestedProxy = new ClassProxy();        
        int nestedProxy_instanceInt = -1;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        
        
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"proxy",self_proxy);        
        setFieldValue(self,"instanceZ",0);        
        setFieldValue(self,"instanceInt",0);        
        setFieldValue(self,"nestedProxy",nestedProxy);        
        
        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy,"nestedProxy",self_proxy_nestedProxy);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        
        /*
         * Configuring variable: nestedProxy
         */
        setFieldValue(nestedProxy,"instanceInt",-1);        
        int result = self.midOneProxyOneInstance(x);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= self.instanceZ ||            
            result <= self.getProxy().getNestedProxy().instanceInt            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result == self.instanceZ ||            
            result == self.getProxy().getNestedProxy().instanceInt ||            
            result == x            
        );        
        
    }
    
    @Test
    public void testmidOneProxyOneInstance1 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();        
        ClassProxy self_proxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy = new ClassProxy();        
        int self_proxy_instanceInt = 0;             
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"proxy",self_proxy);        
        setFieldValue(self,"instanceZ",0);        
        
        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy,"nestedProxy",self_proxy_nestedProxy);        
        setFieldValue(self_proxy,"instanceInt",0);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        int result = self.midOneProxyOneInstance(x);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= self.instanceZ ||            
            result <= self.getProxy().getNestedProxy().instanceInt            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result == self.instanceZ ||            
            result == self.getProxy().getNestedProxy().instanceInt ||            
            result == x            
        );        
        
    }
    
    @Test
    public void testmidOneProxyOneInstance2 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();        
        ClassProxy self_proxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy = new ClassProxy();        
        int self_proxy_instanceInt = 0;              
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"proxy",self_proxy);        
        setFieldValue(self,"instanceZ",1);        
        
        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy,"nestedProxy",self_proxy_nestedProxy);        
        setFieldValue(self_proxy,"instanceInt",0);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        int result = self.midOneProxyOneInstance(x);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= self.instanceZ ||            
            result <= self.getProxy().getNestedProxy().instanceInt            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result == self.instanceZ ||            
            result == self.getProxy().getNestedProxy().instanceInt ||            
            result == x            
        );        
        
    }
    
    @Test
    public void testmidOneProxyOneInstance3 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();        
        ClassProxy self_proxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy = new ClassProxy();        
        int self_proxy_instanceInt = -1;           
        ClassProxy self_proxy_nestedProxy_nestedProxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy_nestedProxy_nestedProxy = new ClassProxy();        
        int self_proxy_nestedProxy_nestedProxy_nestedProxy_instanceInt = 0;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"proxy",self_proxy);        
        setFieldValue(self,"instanceZ",0);        
        
        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy,"nestedProxy",self_proxy_nestedProxy);        
        setFieldValue(self_proxy,"instanceInt",-1);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy,"nestedProxy",self_proxy_nestedProxy_nestedProxy);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy_nestedProxy,"nestedProxy",self_proxy_nestedProxy_nestedProxy_nestedProxy);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy_nestedProxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy_nestedProxy_nestedProxy,"instanceInt",0);        
        int result = self.midOneProxyOneInstance(x);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= self.instanceZ ||            
            result <= self.getProxy().getNestedProxy().instanceInt            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result == self.instanceZ ||            
            result == self.getProxy().getNestedProxy().instanceInt ||            
            result == x            
        );        
        
    }
    
    @Test
    public void testmidOneProxyOneInstance4 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();        
        ClassProxy self_proxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy = new ClassProxy();        
        
        int instanceInt = 0;        
        ClassProxy nestedProxy = new ClassProxy();        
        ClassProxy nestedProxy_nestedProxy = new ClassProxy();        
        ClassProxy nestedProxy_nestedProxy_nestedProxy = new ClassProxy();        
        int nestedProxy_nestedProxy_nestedProxy_instanceInt = 1;        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"proxy",self_proxy);        
        setFieldValue(self,"instanceZ",1);        
        setFieldValue(self,"instanceInt",0);        
        setFieldValue(self,"nestedProxy",nestedProxy);        
        
        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy,"nestedProxy",self_proxy_nestedProxy);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        
        /*
         * Configuring variable: nestedProxy
         */
        setFieldValue(nestedProxy,"nestedProxy",nestedProxy_nestedProxy);        
        
        /*
         * Configuring variable: nestedProxy_nestedProxy
         */
        setFieldValue(nestedProxy_nestedProxy,"nestedProxy",nestedProxy_nestedProxy_nestedProxy);        
        
        /*
         * Configuring variable: nestedProxy_nestedProxy_nestedProxy
         */
        setFieldValue(nestedProxy_nestedProxy_nestedProxy,"instanceInt",1);        
        int result = self.midOneProxyOneInstance(x);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= self.instanceZ ||            
            result <= self.getProxy().getNestedProxy().instanceInt            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result == self.instanceZ ||            
            result == self.getProxy().getNestedProxy().instanceInt ||            
            result == x            
        );        
        
    }
    
    @Test
    public void testmidOneProxyOneInstance5 ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Create the values needed for this test case.
         */
        PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();        
        ClassProxy self_proxy = new ClassProxy();        
        ClassProxy self_proxy_nestedProxy = new ClassProxy();        
        
        /*
         * Create the parameter instances to be passed to the method under test.
         *
         */
        int x = 0;        
        
        /*
         * Configuring variable: self
         */
        setFieldValue(self,"proxy",self_proxy);        
        setFieldValue(self,"instanceZ",0);        
        
        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy,"nestedProxy",self_proxy_nestedProxy);        
        setFieldValue(self_proxy,"instanceInt",0);        
        
        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy,"instanceInt",0);        
        int result = self.midOneProxyOneInstance(x);        
        
        /*
         * Test oracle
         */
        Assert.assertTrue(        
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= x ||            
            result <= self.getProxy().getNestedProxy().instanceInt ||            
            result <= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= x ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result <= self.instanceZ ||            
            result <= self.getProxy().getNestedProxy().instanceInt            
        );        
        
        Assert.assertTrue(        
            result >= self.getProxy().getNestedProxy().instanceInt ||            
            result >= self.instanceZ            
        );        
        
        Assert.assertTrue(        
            result == self.instanceZ ||            
            result == self.getProxy().getNestedProxy().instanceInt ||            
            result == x            
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
