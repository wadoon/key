package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.logic.TermBuilder;

public class TermBuilderHolder {

    private TermBuilder tb;

    private TermBuilderHolder() {}

    private static TermBuilderHolder instance = new TermBuilderHolder();

    public static TermBuilderHolder getInstance() {
        return instance;
    }

    public TermBuilder getTermBuilder() {
        return tb;
    }

    public void setTermBuilder(TermBuilder tb) {
        this.tb = tb;
    }

}
