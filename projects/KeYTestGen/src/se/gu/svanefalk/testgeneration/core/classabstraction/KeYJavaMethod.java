package se.gu.svanefalk.testgeneration.core.classabstraction;

import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.ContractWrapper;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Encapsulates information regarding a single Java method. The information
 * contained in an instance of this class is sufficient to facilitate symbolic
 * execution of the method.
 * 
 * @author christopher
 */
public class KeYJavaMethod {

    /**
     * The class declaring this method.
     */
    private final KeYJavaClass declaringClass;

    /**
     * A wrapper for the an instance of {@link FunctionalOperationContract}
     * specific for this method. Through this contract, we can access the
     * specifications for the method (i.e. mappings between preconditions and
     * postconditions).
     */
    private final ContractWrapper functionalContract;

    /**
     * The {@link IProgramMethod} instance for this method, containing the
     * KeY-specific data for it.
     */
    private final IProgramMethod programMethod;

    KeYJavaMethod(final KeYJavaClass declaringClass,
            final IProgramMethod programMethod,
            final KeYEnvironment<CustomConsoleUserInterface> environment,
            final ContractWrapper functionalContract) {

        this.declaringClass = declaringClass;
        this.programMethod = programMethod;
        this.functionalContract = functionalContract;
    }

    public KeYJavaClass getDeclaringClass() {
        return declaringClass;
    }

    /**
     * Return the {@link InitConfig} instance for this method.
     * 
     * @return the initConfig
     */
    public final InitConfig getInitConfig() {

        return declaringClass.getEnvironment().getInitConfig();
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
        programMethod.getParameters();
        return functionalContract.getParameters();
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
     * Retrieve the preconditions for the method.
     * 
     * @return the preconditions
     */
    public List<Term> getPreconditions() {

        return functionalContract.getPreconditions();
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
     * @return the return type of the method
     */
    public String getReturnType() {

        return programMethod.getReturnType().getName();
    }

    public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
        return declaringClass.getEnvironment();
    }
}