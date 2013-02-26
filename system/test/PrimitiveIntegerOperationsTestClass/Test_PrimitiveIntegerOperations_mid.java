package PrimitiveIntegerOperationsTestClass;

import org.junit.*;
import java.lang.reflect.*;
import java.util.*;
import de.uka.ilkd.key.testgeneration.targetmodels.PrimitiveIntegerOperations;

public  class Test_PrimitiveIntegerOperations_mid {
    
    @Test
    public void testmid0 () {
        int x = -1;
        int y = 0;
        int z = 1;
        int result = self.mid(x,y,z);
        Assert.assertTrue(
            (result == x) ||
            (result == y) ||
            (result == z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= y) ||
            (result <= z)
        );
        
    }
    
    @Test
    public void testmid1 () {
        int x = -1;
        int y = -1;
        int z = 0;
        int result = self.mid(x,y,z);
        Assert.assertTrue(
            (result == x) ||
            (result == y) ||
            (result == z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= y) ||
            (result <= z)
        );
        
    }
    
    @Test
    public void testmid2 () {
        int x = 0;
        int y = -1;
        int z = 0;
        int result = self.mid(x,y,z);
        Assert.assertTrue(
            (result == x) ||
            (result == y) ||
            (result == z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= y) ||
            (result <= z)
        );
        
    }
    
    @Test
    public void testmid3 () {
        int x = 1;
        int y = 0;
        int z = 0;
        int result = self.mid(x,y,z);
        Assert.assertTrue(
            (result == x) ||
            (result == y) ||
            (result == z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= y) ||
            (result <= z)
        );
        
    }
    
    @Test
    public void testmid4 () {
        int x = 1;
        int y = 1;
        int z = 0;
        int result = self.mid(x,y,z);
        Assert.assertTrue(
            (result == x) ||
            (result == y) ||
            (result == z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= y) ||
            (result <= z)
        );
        
    }
    
    @Test
    public void testmid5 () {
        int x = 0;
        int y = 0;
        int z = 0;
        int result = self.mid(x,y,z);
        Assert.assertTrue(
            (result == x) ||
            (result == y) ||
            (result == z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= x) ||
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result >= y) ||
            (result >= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= x) ||
            (result <= y) ||
            (result <= z)
        );
        Assert.assertTrue(
            (result <= y) ||
            (result <= z)
        );
        
    }
    
    
    /**
     * KeYTestGen2 put me here to keep track of your object instances! Don't
     * mind me :)
     */
    private static HashMap<Integer, Object> objectInstances = new HashMap<Integer,Object>();

    
    
    /**
     * This method will retrieve an object instance corresponding to
     * its reference ID.
     */
    private static <T> T getObjectInstance (int reference) {
        return (T)objectInstances.get(reference);
    }
    
    /**
     * Sets a field of some object to a given value
     */
    private static void setFieldValue (Object instance, String fieldName, Object value)
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        Field field = instance.getClass().getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(instance, value );
    }
    
    /**
     * This method will set up the entire repository of object instances needed
     * to execute the test cases declared above.
     */
    @BeforeClass
    public static void createFixtureRepository ()
        throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
        
        /*
         * Instantiate and insert the raw object instances into the repository. After
         * this, finalize the repository setup by setting up the relevant fields
         * of each object instance as necessary
         */
        objectInstances.put(2, new PrimitiveIntegerOperations());
        objectInstances.put(4, new PrimitiveIntegerOperations());
        objectInstances.put(3, new PrimitiveIntegerOperations());
        objectInstances.put(1, new PrimitiveIntegerOperations());
        objectInstances.put(6, new PrimitiveIntegerOperations());
        objectInstances.put(5, new PrimitiveIntegerOperations());
        {
            PrimitiveIntegerOperations instance = getObjectInstance(2);
        }
        
        {
            PrimitiveIntegerOperations instance = getObjectInstance(4);
        }
        
        {
            PrimitiveIntegerOperations instance = getObjectInstance(3);
        }
        
        {
            PrimitiveIntegerOperations instance = getObjectInstance(1);
        }
        
        {
            PrimitiveIntegerOperations instance = getObjectInstance(6);
        }
        
        {
            PrimitiveIntegerOperations instance = getObjectInstance(5);
        }
        
    }
}
