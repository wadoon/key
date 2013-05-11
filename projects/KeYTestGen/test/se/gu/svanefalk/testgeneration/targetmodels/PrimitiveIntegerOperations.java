package se.gu.svanefalk.testgeneration.targetmodels;

/**
 * This class provides various methods which use primitive integer operations,
 * coupled with control assertions of gradually increasing complexity. The
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

    /*
     * @ public normal_behavior
     * 
     * requires (year > 1900) && (year < 2099)
     * 
     * ensures true
     * 
     * @
     */
    public static int easterDate(final int year) {

        int n, a, b, m, q, w, d;

        if ((year < 1900) || (year > 2099)) {

            throw new IllegalArgumentException("Bad year");
        }

        n = year - 1900;
        a = n % 19;
        b = ((7 * a) + 1) / 19;
        m = (((11 * a) + 4) - b) % 29;
        q = n / 4;
        w = ((n + q + 31) - m) % 7;
        d = 25 - m - w;

        if (d > 0) {
            return d;
        } else {
            return 31 + d;
        }
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
    public static int euclidesRecursive(final int a, final int b) {

        if (b == 0) {
            return a;
        } else {
            return PrimitiveIntegerOperations.euclidesRecursive(b, a % b);
        }
    }

    /**
     * @return the staticX
     */
    public static final int getStaticX() {

        return PrimitiveIntegerOperations.staticX;
    }

    /**
     * @return the staticY
     */
    public static final int getStaticY() {

        return PrimitiveIntegerOperations.staticY;
    }

    /**
     * @return the staticZ
     */
    public static final int getStaticZ() {

        return PrimitiveIntegerOperations.staticZ;
    }

    /*@ public normal_behavior
      @ ensures (\result == x) || (\result == y) || (\result == z );
      @ ensures ((\result <= y) && (\result <= z )) || ((\result <= y) &&
          (\result <= x )) || ((\result <= x) && (\result <= z ));
      @ ensures ((\result >= y) && (\result >= z )) || ((\result >= y) &&
          (\result >= x )) || ((\result >= x) && (\result >= z ));
      @*/
    public static int mid(final int x, final int y, final int z) {

        int mid = z;
        if (y < z) {
            if (x < y) {
                mid = y;
            } else if (x <= z) {
                mid = x;
            }
        } else {
            if (x > y) {
                mid = y;
            } else if (x >= z) {
                mid = x;
            }
        }
        return mid;
    }
    
    /*@ public normal_behavior
    @ ensures (\result == x) || (\result == y) || (\result == z );
    @ ensures ((\result <= y) && (\result <= z )) || ((\result <= y) &&
        (\result <= x )) || ((\result <= x) && (\result <= z ));
    @ ensures ((\result >= y) && (\result >= z )) || ((\result >= y) &&
        (\result >= x )) || ((\result >= x) && (\result >= z ));
    @*/
  public static int mid2(final int x, final int y, final int z) {

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
  
  /*@ public normal_behavior
  @ ensures (\result == x) || (\result == y) || (\result == z );
  @ ensures ((\result <= y) && (\result <= z )) || ((\result <= y) &&
      (\result <= x )) || ((\result <= x) && (\result <= z ));
  @ ensures ((\result >= y) && (\result >= z )) || ((\result >= y) &&
      (\result >= x )) || ((\result >= x) && (\result >= z ));
  @*/
public static int mid3(final int x, final int y, final int z) {

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

    public static int midTwoStatic(final int x) {

        int mid = PrimitiveIntegerOperations.staticZ;

        if (PrimitiveIntegerOperations.staticY < PrimitiveIntegerOperations.staticZ) {
            if (x < PrimitiveIntegerOperations.staticY) {
                mid = PrimitiveIntegerOperations.staticY;
            } else if (x < PrimitiveIntegerOperations.staticZ) {

                mid = x;
            }
        } else {

            if (x > PrimitiveIntegerOperations.staticY) {

                mid = PrimitiveIntegerOperations.staticY;
            } else if (x > PrimitiveIntegerOperations.staticZ) {

                mid = x;
            }
        }
        return mid;
    }

    /**
     * @param staticX
     *            the staticX to set
     */
    public static final void setStaticX(final int staticX) {

        PrimitiveIntegerOperations.staticX = staticX;
    }

    /**
     * @param staticY
     *            the staticY to set
     */
    public static final void setStaticY(final int staticY) {

        PrimitiveIntegerOperations.staticY = staticY;
    }

    /**
     * @param staticZ
     *            the staticZ to set
     */
    public static final void setStaticZ(final int staticZ) {

        PrimitiveIntegerOperations.staticZ = staticZ;
    }

    public int instanceX;

    public int instanceY;

    public int instanceZ;

    /*
     * Local refernce variables to simulate work with associated classes
     */
    public ClassProxy proxy = new ClassProxy();

    public PrimitiveIntegerOperations() {
    }

    public PrimitiveIntegerOperations

    (final String a, final String b) {
    }

    /*@ public normal_behavior 
    @ requires true;
    @ ensures true;
    @*/
    public int doStuff(int a, int b,int c, int d) {

        int result = 0;
        
        if((12*a - 5 >= b*5) && (c*6 + 8 <= 2/d))
            result = 1;
        else
            result = 2;
        
        return result;
    }

    /**
     * @return the instanceX
     */
    public final int getInstanceX() {

        return this.instanceX;
    }

    /**
     * @return the instanceY
     */
    public final int getInstanceY() {

        return this.instanceY;
    }

    /**
     * @return the instanceZ
     */
    public final int getInstanceZ() {

        return this.instanceZ;
    }

    /**
     * @return the proxy
     */
    public final ClassProxy getProxy() {

        return this.proxy;
    }

    /*
     * @ public normal_behavior
     * 
     * @ requires (a > b);
     * 
     * @ ensures (\result == a);
     * 
     * @
     */
    public int max(final int a, final int b) {

        int max = a;

        if (max == 1) {
        }

        if (a >= b) {
            max = a;
        } else {
            max = b;
        }

        return max;
    }

    public int maxInstance(final int x) {

        int max = x;

        if (x >= this.instanceY) {
            max = x;
        } else {
            max = this.instanceY;
        }

        return max;
    }

    public int maxProxyInstance(final int x) {

        if (x > this.proxy.nestedProxy.instanceInt) {
            return x;
        } else {
            return this.proxy.nestedProxy.instanceInt;
        }
    }

    public int maxProxyStatic(final int x) {

        if (x >= ClassProxy.staticInt) {
            return x;
        } else {
            return ClassProxy.staticInt;
        }
    }

    public int maxStatic(final int x) {

        int max = x;

        if (x >= PrimitiveIntegerOperations.staticY) {
            max = x;
        } else {
            max = PrimitiveIntegerOperations.staticY;
        }

        return max;
    }

    /*@ public normal_behavior
      @ ensures (\result == x) || (\result == proxy.nestedProxy.instanceInt) ||
          (\result == instanceZ );
      @ ensures ((\result <= proxy.nestedProxy.instanceInt) && (\result <=
          instanceZ )) || ((\result <= proxy.nestedProxy.instanceInt) && (\result
          <= x )) || ((\result <= x) && (\result <= instanceZ));
     @ ensures ((\result >= proxy.nestedProxy.instanceInt) && (\result >=
          instanceZ )) || ((\result >= proxy.nestedProxy.instanceInt) && (\result
          >= x )) || ((\result >= x) && (\result >= instanceZ));
      @*/
    public int midOneProxyOneInstance(final int x) {

        int mid = 0;

        if ((this.proxy == this.proxy.nestedProxy)
                && (x == this.proxy.instanceInt)
                && (this.proxy.nestedProxy.nestedProxy == null)) {
            mid = 15;
        }

        if (this.proxy == null) {
            mid = 16;
        }

        if (this.proxy.instanceInt < this.instanceZ) {
            if (x < this.proxy.nestedProxy.nestedProxy.nestedProxy.instanceInt) {
                mid = this.proxy.nestedProxy.instanceInt;
            } else if (x < this.instanceZ) {

                mid = x;
            }
        } else {

            if (x > this.proxy.nestedProxy.instanceInt) {

                mid = this.proxy.nestedProxy.instanceInt;
            } else if (x > this.instanceZ) {

                mid = this.instanceZ;
            }
        }
        return mid;
    }

    public int midTwoInstance(final int x) {

        int mid = this.instanceZ;

        if (this.instanceY < this.instanceZ) {
            if (x < this.instanceY) {
                mid = this.instanceY;
            } else if (x < this.instanceZ) {

                mid = x;
            }
        } else {

            if (x > this.instanceY) {

                mid = this.instanceY;
            } else if (x > this.instanceZ) {

                mid = x;
            }
        }
        return mid;
    }

    public int midTwoProxy(final int x) {

        int mid = this.proxy.nestedProxy.instanceInt;

        if (this.proxy.instanceInt < this.proxy.nestedProxy.instanceInt) {
            if (x < this.proxy.instanceInt) {
                mid = this.proxy.instanceInt;
            } else if (x < this.proxy.nestedProxy.instanceInt) {

                mid = x;
            }
        } else {

            if (x > this.proxy.instanceInt) {

                mid = this.proxy.instanceInt;
            } else if (x > this.proxy.nestedProxy.instanceInt) {

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

        if (this.proxy != null) {
            return 1;

        } else {
            return 0;
        }

    }

    /**
     * @param instanceX
     *            the instanceX to set
     */
    public final void setInstanceX(final int instanceX) {

        this.instanceX = instanceX;
    }

    /**
     * @param instanceY
     *            the instanceY to set
     */
    public final void setInstanceY(final int instanceY) {

        this.instanceY = instanceY;
    }

    /**
     * @param instanceZ
     *            the instanceZ to set
     */
    public final void setInstanceZ(final int instanceZ) {

        this.instanceZ = instanceZ;
    }

    /**
     * @param proxy
     *            the proxy to set
     */
    public final void setProxy(final ClassProxy proxy) {

        this.proxy = proxy;
    }
}