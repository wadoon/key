package edu.kit.iti.concurrent;

/**
 * Simple lock class for demonstration purposes.
 */
public final class Lock {

    //@ public static ghost Thread holder;

    public static native void lock (Thread t);

    public static native void unlock (Thread t);

}
