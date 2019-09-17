package de.uka.ilkd.key.strategy.conflictbasedinst;

public class ContextSingleton {

    private static Context singleton;

    public static void setContext(Context context) {
        singleton = context;
    }

    public static Context getContext() {
        return singleton;
    }
}
