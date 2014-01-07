package com.csvanefalk.keytestgen.core.classabstraction;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.ContractWrapper;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

import java.util.LinkedList;
import java.util.List;

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

    public FunctionalOperationContract getFunctionalContract() {
        return functionalContract;
    }

    /**
     * A wrapper for the an instance of {@link FunctionalOperationContract}
     * specific for this method. Through this contract, we can access the
     * specifications for the method (i.e. mappings between preconditions and
     * postconditions).
     */
    private final FunctionalOperationContract functionalContract;

    /**
     * The {@link IProgramMethod} instance for this method, containing the
     * KeY-specific data for it.
     */
    private final IProgramMethod programMethod;

    KeYJavaMethod(final KeYJavaClass declaringClass,
                  final IProgramMethod programMethod,
                  final KeYEnvironment<CustomConsoleUserInterface> environment,
                  final FunctionalOperationContract functionalContract) {

        this.declaringClass = declaringClass;
        this.programMethod = programMethod;
        this.functionalContract = functionalContract;
    }

    public KeYJavaClass getDeclaringClass() {
        return declaringClass;
    }

    public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
        return declaringClass.getEnvironment();
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
        final List<IProgramVariable> parameters = new LinkedList<IProgramVariable>();
        for (final ParameterDeclaration declaration : programMethod.getParameters()) {
            parameters.add(declaration.getVariableSpecification().getProgramVariable());
        }
        return parameters;
    }

    /**
     * Retrieve the postconditions for the method.
     *
     * @return the postconditions
     */
    public List<Term> getPostconditions() {

        return functionalContract == null ? null : new ContractWrapper((FunctionalOperationContractImpl) functionalContract)
                .getPostconditions();
    }

    /**
     * Retrieve the preconditions for the method.
     *
     * @return the preconditions
     */
    public List<Term> getPreconditions() {
        return new ContractWrapper((FunctionalOperationContractImpl) functionalContract).getPreconditions();
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
        final KeYJavaType returnType = programMethod.getReturnType();
        if (returnType == KeYJavaType.VOID_TYPE) {
            return "void";
        } else {
            return programMethod.getReturnType().getName();
        }
    }

    /**
     * @return the name of the method
     */
    public String getName() {
        return programMethod.getFullName();
    }

    /**
     * @return true if the method is public, false otherwise.
     */
    public boolean isPublic() {
        return programMethod.isPublic();
    }

    /**
     * @return true if the method is protected, false otherwise.
     */
    public boolean isProtected() {
        return programMethod.isProtected();
    }

    /**
     * @return true if the method is private, false otherwise.
     */
    public boolean isPrivate() {
        return programMethod.isPrivate();
    }

    @Override
    public String toString() {
        return getName();
    }
}