package de.uka.ilkd.key.strategy;

import java.util.concurrent.ThreadFactory;

public class MyThreadFactory implements ThreadFactory {
    private ThreadFactory factory;
    private String name;

    public MyThreadFactory(ThreadFactory factory, String name) {
        super();
        this.factory = factory;
        this.name = name;
    }

    @Override
    public Thread newThread(Runnable r) {
        Thread t = factory.newThread(r);
        t.setName(name + t.getName());
        return t;
    }

}
