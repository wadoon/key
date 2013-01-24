package de.uka.ilkd.key.testgeneration.targetmodels;

/**
 * Some other class, for the purpose of working with variables resident to
 * external classes
 */
public class ClassProxy {

    public static int staticInt;
    public int instanceInt;
    public ClassProxy nestedProxy;

    /**
     * @return the staticInt
     */
    public static final int getStaticInt() {

        return staticInt;
    }

    /**
     * @param staticInt
     *            the staticInt to set
     */
    public static final void setStaticInt(int staticInt) {

        ClassProxy.staticInt = staticInt;
    }

    /**
     * @return the instanceInt
     */
    public final int getInstanceInt() {

        return instanceInt;
    }

    /**
     * @param instanceInt
     *            the instanceInt to set
     */
    public final void setInstanceInt(int instanceInt) {

        this.instanceInt = instanceInt;
    }

    /**
     * @return the nestedProxy
     */
    public final ClassProxy getNestedProxy() {

        return nestedProxy;
    }

    /**
     * @param nestedProxy
     *            the nestedProxy to set
     */
    public final void setNestedProxy(ClassProxy nestedProxy) {

        this.nestedProxy = nestedProxy;
    }
}
