package de.uka.ilkd.key.testgeneration.targetmodels;

/**
 * This class provides various methods which use primitive integer operations,
 * coupled with control statements of gradually increasing complexity. The
 * methods will excercise all available integer operations, in all feasible
 * combinations.
 * 
 * @author christopher
 */
public class PrimitiveIntegerOperations {

    /*
     * Local variables to simulate extra-method dependencies during symbolic
     * execution
     */
    public static int staticX;
    public static int staticY;
    public static int staticZ;

    public int instanceX;
    public int instanceY;
    public int instanceZ;

    /*
     * Local refernce variables to simulate work with associated classes
     */
    public ClassProxy proxy = new ClassProxy();

    public int maxProxyStatic(int x) {

        if (x >= ClassProxy.staticInt) {
            return x;
        }
        else {
            return ClassProxy.staticInt;
        }
    }

    public int maxProxyInstance(int x) {

        if (x > proxy.nestedProxy.instanceInt) {
            return x;
        }
        else {
            return proxy.nestedProxy.instanceInt;
        }
    }

    public int max(int a, int b) {

        int max = 0;

        if (a >= b) {
            max = a;
        }
        else {
            max = a;
        }

        return max;
    }

    public int maxInstance(int x) {

        if (x >= instanceY) {
            return x;
        }
        else {
            return staticY;
        }
    }

    public int maxStatic(int x) {

        if (x >= staticY) {
            return x;
        }
        else {
            return staticY;
        }
    }

    /*
     * @ public normal_behavior
     * 
     * ensures (\result == x) || (\result == y) || (\result == z );
     * 
     * ensures ((\result <= y) && (\result <= z )) || ((\result <= y) &&
     * (\result <= x )) || ((\result <= x) && (\result <= z ));
     * 
     * ensures ((\result >= y) && (\result >= z )) || ((\result >= y) &&
     * (\result >= x )) || ((\result >= x) && (\result >= z ));
     * 
     * @
     */
    public static int mid(int x, int y, int z) {

        int mid = z;

        if (y < z) {
            if (x < y) {
                mid = y;
            }
            else if (x < z) {

                mid = x;
            }
        }
        else {

            if (x > y) {

                mid = y;
            }
            else if (x > z) {

                mid = x;
            }
        }
        return mid;
    }


    public static int midTwoStatic(int x) {

        int mid = staticZ;

        if (staticY < staticZ) {
            if (x < staticY) {
                mid = staticY;
            }
            else if (x < staticZ) {

                mid = x;
            }
        }
        else {

            if (x > staticY) {

                mid = staticY;
            }
            else if (x > staticZ) {

                mid = x;
            }
        }
        return mid;
    }
    
    public int midTwoInstance(int x) {

        int mid = instanceZ;

        if (instanceY < instanceZ) {
            if (x < instanceY) {
                mid = instanceY;
            }
            else if (x < instanceZ) {

                mid = x;
            }
        }
        else {

            if (x > instanceY) {

                mid =instanceY;
            }
            else if (x > instanceZ) {

                mid = x;
            }
        }
        return mid;
    }

    public int midOneProxyOneInstance(int x) {

        int mid = x;

        if (proxy.instanceInt < instanceZ) {
            if (x < proxy.instanceInt) {
                mid = proxy.instanceInt;
            }
            else if (x < instanceZ) {

                mid = x;
            }
        }
        else {

            if (x > proxy.instanceInt) {

                mid = proxy.instanceInt;
            }
            else if (x > instanceZ) {

                mid = x;
            }
        }
        return mid;
    }

    /*
     * @ public normal_behavior
     * 
     * requires (year > 1900) && (year < 2099)
     * 
     * ensures true
     * 
     * @
     */
    public static int easterDate(int year) {

        int n, a, b, m, q, w, d;

        if (year < 1900 || year > 2099) {

            throw new IllegalArgumentException("Bad year");
        }

        n = year - 1900;
        a = n % 19;
        b = (7 * a + 1) / 19;
        m = (11 * a + 4 - b) % 29;
        q = n / 4;
        w = (n + q + 31 - m) % 7;
        d = 25 - m - w;

        if (d > 0) {
            return d;
        }
        else
            return 31 + d;
    }

    /**
     * Use Euclides algorithm to find the greatest common denominator of two
     * integers.
     * 
     * @param a
     * @param b
     * @return
     */
    /*
     * @ public normal_behavior
     * 
     * requires true
     * 
     * ensures true
     * 
     * @
     */
    public static int euclidesRecursive(int a, int b) {

        if (b == 0) {
            return a;
        }
        else {
            return euclidesRecursive(b, a % b);
        }
    }
    

    /**
     * @return the staticX
     */
    public static final int getStaticX() {
    
        return staticX;
    }

    
    /**
     * @param staticX the staticX to set
     */
    public static final void setStaticX(int staticX) {
    
        PrimitiveIntegerOperations.staticX = staticX;
    }

    
    /**
     * @return the staticY
     */
    public static final int getStaticY() {
    
        return staticY;
    }

    
    /**
     * @param staticY the staticY to set
     */
    public static final void setStaticY(int staticY) {
    
        PrimitiveIntegerOperations.staticY = staticY;
    }

    
    /**
     * @return the staticZ
     */
    public static final int getStaticZ() {
    
        return staticZ;
    }

    
    /**
     * @param staticZ the staticZ to set
     */
    public static final void setStaticZ(int staticZ) {
    
        PrimitiveIntegerOperations.staticZ = staticZ;
    }

    
    /**
     * @return the instanceX
     */
    public final int getInstanceX() {
    
        return instanceX;
    }

    
    /**
     * @param instanceX the instanceX to set
     */
    public final void setInstanceX(int instanceX) {
    
        this.instanceX = instanceX;
    }

    
    /**
     * @return the instanceY
     */
    public final int getInstanceY() {
    
        return instanceY;
    }

    
    /**
     * @param instanceY the instanceY to set
     */
    public final void setInstanceY(int instanceY) {
    
        this.instanceY = instanceY;
    }

    
    /**
     * @return the instanceZ
     */
    public final int getInstanceZ() {
    
        return instanceZ;
    }

    
    /**
     * @param instanceZ the instanceZ to set
     */
    public final void setInstanceZ(int instanceZ) {
    
        this.instanceZ = instanceZ;
    }

    
    /**
     * @return the proxy
     */
    public final ClassProxy getProxy() {
    
        return proxy;
    }

    
    /**
     * @param proxy the proxy to set
     */
    public final void setProxy(ClassProxy proxy) {
    
        this.proxy = proxy;
    }
}