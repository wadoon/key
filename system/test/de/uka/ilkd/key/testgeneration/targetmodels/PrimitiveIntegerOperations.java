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

    public int maxOvershadowInstance(int a, int instanceY) {

        if (a >= instanceY) {
            return a;
        }
        else {
            return instanceY;
        }
    }

    public int max(int a, int b) {

        if (a >= b) {
            return a;
        }
        else {
            return b;
        }
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

    public int nested(int a, int b) {

        int i = 0;

        if (a >= b) {
            int c = b;
            int d = a;
            if (a > c) {
                if (a > d) {
                    return a;
                }
            }
        }
        else {
            return b;
        }

        return i;
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
    public static int nonStaticMid(int x, int y, int z) {

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

    /*
     * @ public normal_behavior
     * 
     * ensures (\result == x) || (\result == y) || (\result == externalZ );
     * 
     * ensures ((\result <= y) && (\result <= externalZ )) || ((\result <= y) &&
     * (\result <= x )) || ((\result <= x) && (\result <= externalZ ));
     * 
     * ensures ((\result >= y) && (\result >= externalZ )) || ((\result >= y) &&
     * (\result >= x )) || ((\result >= x) && (\result >= externalZ ));
     * 
     * @
     */
    public int nonStaticMidOneExternal(int x, int y) {

        int mid = instanceZ;

        if (y < instanceZ) {
            if (x < y) {
                mid = y;
            }
            else if (x < instanceZ) {

                mid = x;
            }
        }
        else {

            if (x > y) {

                mid = y;
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
     * ensures (\result == x) || (\result == y) || (\result == externalZ );
     * 
     * ensures ((\result <= y) && (\result <= externalZ )) || ((\result <= y) &&
     * (\result <= x )) || ((\result <= x) && (\result <= externalZ ));
     * 
     * ensures ((\result >= y) && (\result >= externalZ )) || ((\result >= y) &&
     * (\result >= x )) || ((\result >= x) && (\result >= externalZ ));
     * 
     * @
     */
    public int nonStaticMidOneExternalProxy(int x, int y) {

        int mid = proxy.instanceInt;

        if (y < proxy.instanceInt) {
            if (x < y) {
                mid = y;
            }
            else if (x < proxy.instanceInt) {

                mid = x;
            }
        }
        else {

            if (x > y) {

                mid = y;
            }
            else if (x > proxy.instanceInt) {

                mid = x;
            }
        }
        return mid;
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
    public static int midExperimental(int x, int y) {

        int zInt = 0;
        int mid = zInt;

        if (y < zInt) {
            int k = x;
            if (k < y) {

                mid = y;
            }
            else if (x < zInt) {

                mid = x;
            }
        }
        else {

            if (x > y) {

                mid = y;
            }
            else if (x > zInt) {

                mid = x;
            }
        }
        return mid;
    }

    /*
     * @ public normal_behavior
     * 
     * ensures (\result == x) || (\result == y) || (\result == externalZ );
     * 
     * ensures ((\result <= y) && (\result <= externalZ )) || ((\result <= y) &&
     * (\result <= x )) || ((\result <= x) && (\result <= externalZ ));
     * 
     * ensures ((\result >= y) && (\result >= externalZ )) || ((\result >= y) &&
     * (\result >= x )) || ((\result >= x) && (\result >= externalZ ));
     * 
     * @
     */
    public static int midOneExternal(int x, int y) {

        int mid = staticZ;

        if (y < staticZ) {
            if (x < y) {
                mid = y;
            }
            else if (x < staticZ) {

                mid = x;
            }
        }
        else {

            if (x > y) {

                mid = y;
            }
            else if (x > staticZ) {

                mid = x;
            }
        }
        return mid;
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
    public static int midTwoExternal(int x) {

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
    public static int midThreeExternal() {

        int mid = staticZ;

        if (staticY < staticZ) {
            if (staticX < staticY) {
                mid = staticY;
            }
            else if (staticX < staticZ) {

                mid = staticX;
            }
        }
        else {

            if (staticX > staticY) {

                mid = staticY;
            }
            else if (staticX > staticZ) {

                mid = staticX;
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
}