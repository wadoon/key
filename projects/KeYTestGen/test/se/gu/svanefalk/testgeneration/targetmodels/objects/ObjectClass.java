package se.gu.svanefalk.testgeneration.targetmodels.objects;

import se.gu.svanefalk.testgeneration.targetmodels.unclassified.ClassProxy;

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
