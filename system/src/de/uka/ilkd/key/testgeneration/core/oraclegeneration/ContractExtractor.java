package de.uka.ilkd.key.testgeneration.core.oraclegeneration;

import java.util.List;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ContractWrapper;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

/**
 * Provides various utility methods for extracting and processing the
 * {@link FunctionalOperationContract} information for Java methods.
 * 
 * @author christopher
 */
public enum ContractExtractor {
    INSTANCE;

    /**
     * Searches the symbolic execution tree for the first occurence of a
     * {@link IExecutionMethodCall} node - due to the way the tree is
     * costructed, this should (?) always be a call to the method for which we
     * desire to generate test cases.
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return an {@link IExecutionMethodCall} node corresponding to the root
     *         method call
     * @throws OracleGeneratorException
     *             failure to locate the method is always exceptional
     */
    public Term extractPostCondition(IExecutionStartNode root)
            throws OracleGeneratorException {

        IExecutionMethodCall methodCallNode = getMethodCallNode(root);
        FunctionalOperationContract contract = getContracts(methodCallNode);

        /*
         * This is an ugly hack, but for now I do not see any more
         * straightforward way of extracting the postconditions, which is all I
         * really need. The standard implementation of
         * FunctionalOperationContract appears to be structured exclusively for
         * use within the Proof context.
         */
        ContractWrapper contractWrapper = new ContractWrapper(
                (FunctionalOperationContractImpl) contract);

        List<Term> postconditions = contractWrapper.getPostconditions();

        return null;
    }

    /**
     * Searches the symbolic execution tree for the first occurence of a
     * {@link IExecutionMethodCall} node - due to the way the tree is
     * costructed, this should (?) always be a call to the method for which we
     * desire to generate test cases.
     * 
     * @param root
     *            the root of the symbolic execution tree
     * @return an {@link IExecutionMethodCall} node corresponding to the root
     *         method call
     * @throws OracleGeneratorException
     *             failure to locate the method is always exceptional
     */
    private IExecutionMethodCall getMethodCallNode(IExecutionStartNode root)
            throws OracleGeneratorException {

        ExecutionNodePreorderIterator iterator = new ExecutionNodePreorderIterator(
                root);

        while (iterator.hasNext()) {

            IExecutionNode next = iterator.next();

            if (next instanceof IExecutionMethodCall) {
                return (IExecutionMethodCall) next;
            }
        }

        throw new OracleGeneratorException(
                "FATAL: unable to locate root method");
    }

    /**
     * Extracts the {@link FunctionalOperationContract} instances for a method
     * call represented by a specific{@link IExecutionMethodCall} node.
     * 
     * @param methodCallNode
     *            the symbolic execution node corresponding to the method call
     * @return the contract for the method
     * @throws OracleGeneratorException
     *             failure to find a contract for the method is always
     *             exceptional
     */
    private FunctionalOperationContract getContracts(
            IExecutionMethodCall methodCallNode)
            throws OracleGeneratorException {

        SpecificationRepository specificationRepository = methodCallNode
                .getServices().getSpecificationRepository();

        /*
         * Extract the abstract representation of the method itself, as well as
         * the type of the class which contains it. Use this information in
         * order to retrieve the specification contracts which exist for the
         * method.
         * 
         * For now, we assume that there will only be one contract per method, I
         * am not sure how to deal with situations where there is more than one
         * (or exactly what these extra contracts would mean in practice)
         */
        IProgramMethod programMethod = methodCallNode.getProgramMethod();
        KeYJavaType containerClass = programMethod.getContainerType();
        for (FunctionalOperationContract contract : specificationRepository
                .getOperationContracts(containerClass, programMethod)) {
            return contract;
        }

        throw new OracleGeneratorException(
                "FATAL: Unable to find specification contract for method: "
                        + programMethod);
    }

}
