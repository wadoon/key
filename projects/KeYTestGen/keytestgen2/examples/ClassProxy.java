package se.gu.svanefalk.testgeneration.targetmodels;

/**
 * Some other class, for the purpose of working with variables resident to
 * external classes
 */
public class ClassProxy {

    public static int staticInt;

    /**
     * @return the staticInt
     */
    public static final int getStaticInt() {

        return ClassProxy.staticInt;
    }

    /**
     * @param staticInt
     *            the staticInt to set
     */
    public static final void setStaticInt(final int staticInt) {

        ClassProxy.staticInt = staticInt;
    }

    public int instanceInt;

    public ClassProxy nestedProxy;

    public boolean compare(final int x) {
        return x > 0;
    }

    /**
     * @return the instanceInt
     */
    public final int getInstanceInt() {

        return instanceInt;
    }

    /**
     * @return the nestedProxy
     */
    public final ClassProxy getNestedProxy() {

        return nestedProxy;
    }

    /**
     * @param instanceInt
     *            the instanceInt to set
     */
    public final void setInstanceInt(final int instanceInt) {

        this.instanceInt = instanceInt;
    }

    /**
     * @param nestedProxy
     *            the nestedProxy to set
     */
    public final void setNestedProxy(final ClassProxy nestedProxy) {

        this.nestedProxy = nestedProxy;
    }
}
