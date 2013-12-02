package com.csvanefalk.keytestgen.targetmodels.own;


public class ObjectClass {

    private ClassProxy proxy;
    int instanceZ;

    /*
     *@ public normal_behavior
     * 
     *@ ensures true;
     * 
     *@
     */
    public ClassProxy max_object(final ClassProxy a, final ClassProxy b) {

        if (a.instanceInt > b.instanceInt) {
            return a;
        } else {
            return b;
        }
    }

    /*
     *@ public normal_behavior
     * 
     * @ ensures (\result == x) || (\result == proxy.nestedProxy.instanceInt) ||
     * (\result == instanceZ );
     * 
     * @ ensures ((\result <= proxy.nestedProxy.instanceInt) && (\result <=
     * instanceZ )) || ((\result <= proxy.nestedProxy.instanceInt) && (\result
     * <= x )) || ((\result <= x) && (\result <= instanceZ));
     * 
     * @ ensures ((\result >= proxy.nestedProxy.instanceInt) && (\result >=
     * instanceZ )) || ((\result >= proxy.nestedProxy.instanceInt) && (\result
     * >= x )) || ((\result >= x) && (\result >= instanceZ));
     * 
     * @
     */
    public int midOneProxyOneInstance(final int x) {

        int mid = 0;

        if ((proxy == proxy.nestedProxy) && (x == proxy.instanceInt)
                && (proxy.nestedProxy.nestedProxy == null)) {
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
}
