import org.junit.Assert;
import org.junit.Test;

import se.gu.svanefalk.testgeneration.targetmodels.PrimitiveIntegerOperations;

public class Test_PrimitiveIntegerOperations_mid {

    @SuppressWarnings("static-access")
    @Test
    public void testmid0() throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {

        /*
         * Create the values needed for this test case.
         */
        final PrimitiveIntegerOperations self = new PrimitiveIntegerOperations();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;
        final int y = 1;
        final int z = 2;

        /*
         * Configuring variable: self
         */
        final int result = self.mid(x, y, z);

        /*
         * Test oracle
         */
        Assert.assertTrue((result == y) || (result == x) || (result == z));
        Assert.assertTrue((result >= y) || (result >= x));
        Assert.assertTrue((result >= z) || (result >= y));
        Assert.assertTrue((result <= z) || (result <= x));
        Assert.assertTrue((result >= z) || (result >= x));
        Assert.assertTrue((result <= y) || (result <= x));
        Assert.assertTrue((result <= z) || (result <= y) || (result <= y)
                || (result <= z) || (result <= x));
        Assert.assertTrue((result >= z) || (result >= y) || (result >= x));
    }

    @Test
    public void testmid1() throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {

        new PrimitiveIntegerOperations();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;
        final int y = 0;
        final int z = 0;

        /*
         * Configuring variable: self
         */
        final int result = PrimitiveIntegerOperations.mid(x, y, z);

        /*
         * Test oracle
         */
        Assert.assertTrue((result == y) || (result == x) || (result == z));

        Assert.assertTrue((result >= y) || (result >= x));

        Assert.assertTrue((result >= z) || (result >= y));

        Assert.assertTrue((result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= x));

        Assert.assertTrue((result <= y) || (result <= x));

        Assert.assertTrue((result <= z) || (result <= y) || (result <= y)
                || (result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= y) || (result >= x));

    }

    @Test
    public void testmid2() throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {

        new PrimitiveIntegerOperations();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;
        final int y = 0;
        final int z = 0;

        /*
         * Configuring variable: self
         */
        final int result = PrimitiveIntegerOperations.mid(x, y, z);

        /*
         * Test oracle
         */
        Assert.assertTrue((result == y) || (result == x) || (result == z));

        Assert.assertTrue((result >= y) || (result >= x));

        Assert.assertTrue((result >= z) || (result >= y));

        Assert.assertTrue((result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= x));

        Assert.assertTrue((result <= y) || (result <= x));

        Assert.assertTrue((result <= z) || (result <= y) || (result <= y)
                || (result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= y) || (result >= x));

    }

    @Test
    public void testmid3() throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {

        new PrimitiveIntegerOperations();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;
        final int y = 0;
        final int z = 0;

        /*
         * Configuring variable: self
         */
        final int result = PrimitiveIntegerOperations.mid(x, y, z);

        /*
         * Test oracle
         */
        Assert.assertTrue((result == y) || (result == x) || (result == z));

        Assert.assertTrue((result >= y) || (result >= x));

        Assert.assertTrue((result >= z) || (result >= y));

        Assert.assertTrue((result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= x));

        Assert.assertTrue((result <= y) || (result <= x));

        Assert.assertTrue((result <= z) || (result <= y) || (result <= y)
                || (result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= y) || (result >= x));

    }

    @Test
    public void testmid4() throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {

        new PrimitiveIntegerOperations();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;
        final int y = 0;
        final int z = 0;

        /*
         * Configuring variable: self
         */
        final int result = PrimitiveIntegerOperations.mid(x, y, z);

        /*
         * Test oracle
         */
        Assert.assertTrue((result == y) || (result == x) || (result == z));

        Assert.assertTrue((result >= y) || (result >= x));

        Assert.assertTrue((result >= z) || (result >= y));

        Assert.assertTrue((result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= x));

        Assert.assertTrue((result <= y) || (result <= x));

        Assert.assertTrue((result <= z) || (result <= y) || (result <= y)
                || (result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= y) || (result >= x));

    }

    @Test
    public void testmid5() throws NoSuchFieldException, SecurityException,
            IllegalArgumentException, IllegalAccessException {

        new PrimitiveIntegerOperations();

        /*
         * Create the parameter instances to be passed to the method under test.
         */
        final int x = 0;
        final int y = 0;
        final int z = 0;

        /*
         * Configuring variable: self
         */
        final int result = PrimitiveIntegerOperations.mid(x, y, z);

        /*
         * Test oracle
         */
        Assert.assertTrue((result == y) || (result == x) || (result == z));

        Assert.assertTrue((result >= y) || (result >= x));

        Assert.assertTrue((result >= z) || (result >= y));

        Assert.assertTrue((result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= x));

        Assert.assertTrue((result <= y) || (result <= x));

        Assert.assertTrue((result <= z) || (result <= y) || (result <= y)
                || (result <= z) || (result <= x));

        Assert.assertTrue((result >= z) || (result >= y) || (result >= x));

    }
}