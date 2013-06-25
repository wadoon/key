package se.gu.svanefalk.testgeneration.targetmodels.own;

import se.gu.svanefalk.testgeneration.targetmodels.own.deps.ClassProxy;


public class ObjectClass {

    /*
     * @ public normal_behavior
     * 
     * @ ensures true;
     * 
     * @
     */
    public ClassProxy max(final ClassProxy a, final ClassProxy b) {

        if (a.instanceInt > b.instanceInt) {
            return a;
        } else {
            return b;
        }
    }
}
