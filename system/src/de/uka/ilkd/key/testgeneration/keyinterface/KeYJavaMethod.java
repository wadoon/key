package de.uka.ilkd.key.testgeneration.keyinterface;

import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.ContractWrapper;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * Encapsulates information regarding a single Java method. The information
 * contained in an instance of this class is sufficient to facilitate symbolic
 * execution of the method.
 * 
 * @author christopher
 */
public class KeYJavaMethod {

    /**
     * The {@link IProgramMethod} instance for this method, containing the
     * KeY-specific data for it.
     */
    private final IProgramMethod programMethod;

    /**
     * The {@link InitConfig} instance for the class which this method is part
     * of.
     */
    private final InitConfig initConfig;

    /**
     * A wrapper for the an instance of {@link FunctionalOperationContract}
     * specific for this method. Through this contract, we can access the
     * specifications for the method (i.e. mappings between preconditions and
     * postconditions).
     */
    private final ContractWrapper functionalContract;

    KeYJavaMethod(IProgramMethod programMethod, InitConfig initConfig,
            ContractWrapper functionalContract) {

        this.programMethod = programMethod;
        this.initConfig = initConfig;
        this.functionalContract = functionalContract;
    }

    /**
     * Retrieve the preconditions for the method.
     * 
     * @return the preconditions
     */
    public List<Term> getPreconditions() {

        return functionalContract.getPreconditions();
    }

    /**
     * Retrieve the postconditions for the method.
     * 
     * @return the postconditions
     */
    public List<Term> getPostconditions() {

        return functionalContract.getPostconditions();
    }

    /**
     * Get the parameters for this method.
     * 
     * @return
     */
    public List<IProgramVariable> getParameters() {

        /*
         * TODO: This violates the abstraction in a very ugly way, is there no
         * nicer way to get the parameters?
         */
        return functionalContract.getParameters();
    }

    /**
     * Retrieve the {@link IProgramMethod} instance for this method.
     * 
     * @return the programMethod
     */
    public IProgramMethod getProgramMethod() {

        return programMethod;
    }

    /**
     * Return the {@link InitConfig} instance for this method.
     * 
     * @return the initConfig
     */
    public final InitConfig getInitConfig() {

        return initConfig;
    }

    /**
     * @return the return type of the method
     */
    public String getReturnType() {

        return programMethod.getReturnType().getName();
    }
}