package de.uka.ilkd.key.strategy.conflictbasedinst;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;

public class CbiServices {

    private static TermBuilder termBuiler;
    private static TermFactory termFactory;
    private static Services services;

    public static TermBuilder getTermBuiler() {
        return termBuiler;
    }
    public static void setTermBuiler(TermBuilder termBuiler) {
        CbiServices.termBuiler = termBuiler;
    }
    public static TermFactory getTermFactory() {
        return termFactory;
    }
    public static void setTermFactory(TermFactory termFactory) {
        CbiServices.termFactory = termFactory;
    }
    public static Services getServices() {
        return services;
    }
    public static void setServices(Services services) {
        CbiServices.services = services;
    }


}
