package de.uka.ilkd.key.testgeneration.keyinterface;

import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;

/**
 * Encapsulates information regarding a single Java method. The information contained in an instance
 * of this class is sufficient to facilitate symbolic execution of the method.
 * 
 * @author christopher
 */
public class KeYJavaMethod {

    /**
     * The {@link IProgramMethod} instance for this method, containing the KeY-specific data for it.
     */
    private final IProgramMethod programMethod;

    /**
     * The {@link InitConfig} instance for the class which this method is part of.
     */
    private final InitConfig initConfig;

    /**
     * The preconditions for this method
     */
    private List<Term> preconditions;

    KeYJavaMethod(
            IProgramMethod programMethod,
            InitConfig initConfig,
            List<Term> preconditions) {

        this.programMethod = programMethod;
        this.initConfig = initConfig;
        this.preconditions = preconditions;
    }

    /**
     * @return the preconditions
     */
    final List<Term> getPreconditions() {

        return preconditions;
    }

    /**
     * @return the programMethod
     */
    final IProgramMethod getProgramMethod() {

        return programMethod;
    }

    /**
     * @return the initConfig
     */
    final InitConfig getInitConfig() {

        return initConfig;
    }

}
