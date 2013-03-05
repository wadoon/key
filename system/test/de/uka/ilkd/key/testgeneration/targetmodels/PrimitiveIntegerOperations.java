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

    public 
    
        PrimitiveIntegerOperations(
                ) {}
    
    public         
        PrimitiveIntegerOperations
        
            (String 
                    a, 
                        String b) {}
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
        } else {
            return ClassProxy.staticInt;
        }
    }

    public int maxProxyInstance(int x) {

        if (x > proxy.nestedProxy.instanceInt) {
            return x;
        } else {
            return proxy.nestedProxy.instanceInt;
        }
    }

    /*@ public normal_behavior
     @ requires (a > b);
     @ ensures (\result == a);
     @*/
    public int max(int a, int b) {

        int max = a;

        if (max == 1) {
            int x = 5;
        }

        if (a >= b) {
            max = a;
        } else {
            max = b;
        }

        return max;
    }

    public int maxInstance(int x) {

        int max = x;

        if (x >= instanceY) {
            max = x;
        } else {
            max = instanceY;
        }

        return max;
    }

    public int maxStatic(int x) {

        int max = x;

        if (x >= staticY) {
            max = x;
        } else {
            max = staticY;
        }

        return max;
    }

    /*@ public normal_behavior   
     @ ensures (\result == x) || (\result == y) || (\result == z );      
     @ ensures ((\result <= y) && (\result <= z )) || ((\result <= y) && (\result <= x )) || ((\result <= x) && (\result <= z ));      
     @ ensures ((\result >= y) && (\result >= z )) || ((\result >= y) && (\result >= x )) || ((\result >= x) && (\result >= z ));      
     @*/
    public static int mid(int x, int y, int z) {

        int mid = z;

        if (y < z) {
            if (x < y) {
                mid = y;
            } else if (x < z) {

                mid = x;
            }
        } else {

            if (x > y) {

                mid = y;
            } else if (x > z) {

                mid = x;
            }
        }
        return mid;
    }

    /*
     * @ public normal_behavior
     * 
     * @ ensures true;
     * 
     * @
     */
    public int references() {

        if (proxy != null) {
            return 1;

        } else {
            return 0;
        }

    }

    public static int midTwoStatic(int x) {

        int mid = staticZ;

        if (staticY < staticZ) {
            if (x < staticY) {
                mid = staticY;
            } else if (x < staticZ) {

                mid = x;
            }
        } else {

            if (x > staticY) {

                mid = staticY;
            } else if (x > staticZ) {

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
            } else if (x < instanceZ) {

                mid = x;
            }
        } else {

            if (x > instanceY) {

                mid = instanceY;
            } else if (x > instanceZ) {

                mid = x;
            }
        }
        return mid;
    }

    public int midTwoProxy(int x) {

        int mid = proxy.nestedProxy.instanceInt;

        if (proxy.instanceInt < proxy.nestedProxy.instanceInt) {
            if (x < proxy.instanceInt) {
                mid = proxy.instanceInt;
            } else if (x < proxy.nestedProxy.instanceInt) {

                mid = x;
            }
        } else {

            if (x > proxy.instanceInt) {

                mid = proxy.instanceInt;
            } else if (x > proxy.nestedProxy.instanceInt) {

                mid = x;
            }
        }
        return mid;
    }


    /*@ public normal_behavior   
    @ ensures (\result == x) || (\result == proxy.nestedProxy.instanceInt) || (\result == instanceZ );      
    @ ensures ((\result <= proxy.nestedProxy.instanceInt) && (\result <= instanceZ )) || ((\result <= proxy.nestedProxy.instanceInt) && (\result <= x )) || ((\result <= x) && (\result <= instanceZ));      
    @ ensures ((\result >= proxy.nestedProxy.instanceInt) && (\result >= instanceZ )) || ((\result >= proxy.nestedProxy.instanceInt) && (\result >= x )) || ((\result >= x) && (\result >= instanceZ));      
    @*/
    public int midOneProxyOneInstance(int x) {

        int mid = 0;
        
        if (proxy == proxy.nestedProxy && x == proxy.instanceInt
                && proxy.nestedProxy.nestedProxy == null) {
            mid = 15;
        }
    
        if (proxy == null) {
            mid = 16;
        }

        if (proxy.instanceInt < instanceZ) {
            if (x < proxy.nestedProxy.nestedProxy.nestedProxy.instanceInt) {
                mid = proxy.nestedProxy.instanceInt;
            } else if (x < instanceZ) {

                mid = x;
            }
        } else {

            if (x > proxy.nestedProxy.instanceInt) {

                mid = proxy.nestedProxy.instanceInt;
            } else if (x > instanceZ) {

                mid = instanceZ;
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
        } else
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
        } else {
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
     * @param staticX
     *            the staticX to set
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
     * @param staticY
     *            the staticY to set
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
     * @param staticZ
     *            the staticZ to set
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
     * @param instanceX
     *            the instanceX to set
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
     * @param instanceY
     *            the instanceY to set
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
     * @param instanceZ
     *            the instanceZ to set
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
     * @param proxy
     *            the proxy to set
     */
    public final void setProxy(ClassProxy proxy) {

        this.proxy = proxy;
    }
}