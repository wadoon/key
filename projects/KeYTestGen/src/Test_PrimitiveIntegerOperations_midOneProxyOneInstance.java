import java.lang.reflect.Field;

import org.junit.Assert;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.targetmodels.ClassProxy;
import se.gu.svanefalk.testgeneration.targetmodels.PrimitiveIntegerOperations;

public class Test_PrimitiveIntegerOperations_midOneProxyOneInstance {

    /**
     * Sets a field of some object to a given value
     */
    private void setFieldValue(final Object instance, final String fieldName,
            final Object value) throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {
        final Field field = instance.getClass().getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(instance, value);
    }

    @Test
    public void testmidOneProxyOneInstance0() throws NoSuchFieldException,
            SecurityException, IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();
        final ClassProxy self_proxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy = new ClassProxy();
        final ClassProxy nestedProxy = new ClassProxy();
        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;

        /*
         * Configuring variable: self
         */
        setFieldValue(self, "proxy", self_proxy);
        setFieldValue(self, "instanceZ", 0);
        setFieldValue(self, "instanceInt", 0);
        setFieldValue(self, "nestedProxy", nestedProxy);

        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy, "nestedProxy", self_proxy_nestedProxy);

        /*
         * Configuring variable: self_proxy_nestedProxy
         */

        /*
         * Configuring variable: nestedProxy
         */
        setFieldValue(nestedProxy, "instanceInt", -1);
        final int result = self.midOneProxyOneInstance(x);

        /*
         * Test oracle
         */
        Assert.assertTrue((result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x));

        Assert.assertTrue((result <= x) || (result <= self.instanceZ));

        Assert.assertTrue((result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result <= self.instanceZ)
                || (result <= self.getProxy().getNestedProxy().instanceInt));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= self.instanceZ));

        Assert.assertTrue((result == self.instanceZ)
                || (result == self.getProxy().getNestedProxy().instanceInt)
                || (result == x));

    }

    @Test
    public void testmidOneProxyOneInstance1() throws NoSuchFieldException,
            SecurityException, IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();
        final ClassProxy self_proxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy = new ClassProxy();
        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;

        /*
         * Configuring variable: self
         */
        setFieldValue(self, "proxy", self_proxy);
        setFieldValue(self, "instanceZ", 0);

        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy, "nestedProxy", self_proxy_nestedProxy);
        setFieldValue(self_proxy, "instanceInt", 0);

        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        final int result = self.midOneProxyOneInstance(x);

        /*
         * Test oracle
         */
        Assert.assertTrue((result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x));

        Assert.assertTrue((result <= x) || (result <= self.instanceZ));

        Assert.assertTrue((result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result <= self.instanceZ)
                || (result <= self.getProxy().getNestedProxy().instanceInt));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= self.instanceZ));

        Assert.assertTrue((result == self.instanceZ)
                || (result == self.getProxy().getNestedProxy().instanceInt)
                || (result == x));

    }

    @Test
    public void testmidOneProxyOneInstance2() throws NoSuchFieldException,
            SecurityException, IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();
        final ClassProxy self_proxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy = new ClassProxy();
        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;

        /*
         * Configuring variable: self
         */
        setFieldValue(self, "proxy", self_proxy);
        setFieldValue(self, "instanceZ", 1);

        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy, "nestedProxy", self_proxy_nestedProxy);
        setFieldValue(self_proxy, "instanceInt", 0);

        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        final int result = self.midOneProxyOneInstance(x);

        /*
         * Test oracle
         */
        Assert.assertTrue((result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x));

        Assert.assertTrue((result <= x) || (result <= self.instanceZ));

        Assert.assertTrue((result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result <= self.instanceZ)
                || (result <= self.getProxy().getNestedProxy().instanceInt));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= self.instanceZ));

        Assert.assertTrue((result == self.instanceZ)
                || (result == self.getProxy().getNestedProxy().instanceInt)
                || (result == x));

    }

    @Test
    public void testmidOneProxyOneInstance3() throws NoSuchFieldException,
            SecurityException, IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();
        final ClassProxy self_proxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy_nestedProxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy_nestedProxy_nestedProxy = new ClassProxy();
        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;

        /*
         * Configuring variable: self
         */
        setFieldValue(self, "proxy", self_proxy);
        setFieldValue(self, "instanceZ", 0);

        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy, "nestedProxy", self_proxy_nestedProxy);
        setFieldValue(self_proxy, "instanceInt", -1);

        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy, "nestedProxy",
                self_proxy_nestedProxy_nestedProxy);

        /*
         * Configuring variable: self_proxy_nestedProxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy_nestedProxy, "nestedProxy",
                self_proxy_nestedProxy_nestedProxy_nestedProxy);

        /*
         * Configuring variable: self_proxy_nestedProxy_nestedProxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy_nestedProxy_nestedProxy,
                "instanceInt", 0);
        final int result = self.midOneProxyOneInstance(x);

        /*
         * Test oracle
         */
        Assert.assertTrue((result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x));

        Assert.assertTrue((result <= x) || (result <= self.instanceZ));

        Assert.assertTrue((result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result <= self.instanceZ)
                || (result <= self.getProxy().getNestedProxy().instanceInt));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= self.instanceZ));

        Assert.assertTrue((result == self.instanceZ)
                || (result == self.getProxy().getNestedProxy().instanceInt)
                || (result == x));

    }

    @Test
    public void testmidOneProxyOneInstance4() throws NoSuchFieldException,
            SecurityException, IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();
        final ClassProxy self_proxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy = new ClassProxy();

        final ClassProxy nestedProxy = new ClassProxy();
        final ClassProxy nestedProxy_nestedProxy = new ClassProxy();
        final ClassProxy nestedProxy_nestedProxy_nestedProxy = new ClassProxy();
        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;

        /*
         * Configuring variable: self
         */
        setFieldValue(self, "proxy", self_proxy);
        setFieldValue(self, "instanceZ", 1);
        setFieldValue(self, "instanceInt", 0);
        setFieldValue(self, "nestedProxy", nestedProxy);

        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy, "nestedProxy", self_proxy_nestedProxy);

        /*
         * Configuring variable: self_proxy_nestedProxy
         */

        /*
         * Configuring variable: nestedProxy
         */
        setFieldValue(nestedProxy, "nestedProxy", nestedProxy_nestedProxy);

        /*
         * Configuring variable: nestedProxy_nestedProxy
         */
        setFieldValue(nestedProxy_nestedProxy, "nestedProxy",
                nestedProxy_nestedProxy_nestedProxy);

        /*
         * Configuring variable: nestedProxy_nestedProxy_nestedProxy
         */
        setFieldValue(nestedProxy_nestedProxy_nestedProxy, "instanceInt", 1);
        final int result = self.midOneProxyOneInstance(x);

        /*
         * Test oracle
         */
        Assert.assertTrue((result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x));

        Assert.assertTrue((result <= x) || (result <= self.instanceZ));

        Assert.assertTrue((result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result <= self.instanceZ)
                || (result <= self.getProxy().getNestedProxy().instanceInt));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= self.instanceZ));

        Assert.assertTrue((result == self.instanceZ)
                || (result == self.getProxy().getNestedProxy().instanceInt)
                || (result == x));

    }

    @Test
    public void testmidOneProxyOneInstance5() throws NoSuchFieldException,
            SecurityException, IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();
        final ClassProxy self_proxy = new ClassProxy();
        final ClassProxy self_proxy_nestedProxy = new ClassProxy();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;

        /*
         * Configuring variable: self
         */
        setFieldValue(self, "proxy", self_proxy);
        setFieldValue(self, "instanceZ", 0);

        /*
         * Configuring variable: self_proxy
         */
        setFieldValue(self_proxy, "nestedProxy", self_proxy_nestedProxy);
        setFieldValue(self_proxy, "instanceInt", 0);

        /*
         * Configuring variable: self_proxy_nestedProxy
         */
        setFieldValue(self_proxy_nestedProxy, "instanceInt", 0);
        final int result = self.midOneProxyOneInstance(x);

        /*
         * Test oracle
         */
        Assert.assertTrue((result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x));

        Assert.assertTrue((result <= x) || (result <= self.instanceZ));

        Assert.assertTrue((result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= x)
                || (result <= self.getProxy().getNestedProxy().instanceInt)
                || (result <= self.instanceZ));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= x) || (result >= self.instanceZ));

        Assert.assertTrue((result <= self.instanceZ)
                || (result <= self.getProxy().getNestedProxy().instanceInt));

        Assert.assertTrue((result >= self.getProxy().getNestedProxy().instanceInt)
                || (result >= self.instanceZ));

        Assert.assertTrue((result == self.instanceZ)
                || (result == self.getProxy().getNestedProxy().instanceInt)
                || (result == x));
    }
}
