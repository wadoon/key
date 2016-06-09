/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.informationflow.po;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.key_project.common.core.logic.Named;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.ContractFactory;


/**
 *
 * @author christoph
 */
public class BlockExecutionPO extends AbstractInfFlowPO
        implements InfFlowCompositePO {

    private final BlockContract contract;
    private final ProofObligationVars symbExecVars;
    private final Goal initiatingGoal;
    private final ExecutionContext context;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the
     * according taclets, program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    /** To be used only for auxiliary proofs where the services object of
     * the actual proof has to be used instead of the initial services form
     * the InitConfig.
     */
    public BlockExecutionPO(InitConfig initConfig,
                            BlockContract contract,
                            ProofObligationVars symbExecVars,
                            Goal initiatingGoal,
                            ExecutionContext context,
                            Services services) {
        this(initConfig, contract, symbExecVars, initiatingGoal, context);
        this.environmentServices = services;
    }

    public BlockExecutionPO(InitConfig initConfig,
                            BlockContract contract,
                            ProofObligationVars symbExecVars,
                            Goal initiatingGoal,
                            ExecutionContext context) {
        super(initConfig,
              ContractFactory.generateContractName(contract.getName(), contract.getKJT(),
                                                   contract.getTarget(),
                                                   contract.getTarget().getContainerType(),
                                                   contract.getBlock().getStartPosition().getLine()));
        this.contract = contract;
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
        this.context = context;
    }

    @Override
    public void readProblem() throws ProofInputException {
        final Services proofServices = postInit();

        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(contract, symbExecVars,
                                                 context, environmentServices);

        // symbolic execution
        final JavaDLTerm symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.BLOCK_EXEC_WITH_PRE);

        // final symbolic execution term
        final JavaDLTerm finalTerm = tb.applyElementary(symbExecVars.pre.heap,
                                                  tb.not(symExec));

        // register final term
        assignPOTerms(finalTerm);

        // add class axioms
        final Proof initiatingProof = initiatingGoal.proof();
        if (initiatingProof != null) {
            // proof is not loaded
            final AbstractOperationPO initiatingPO =
                    (AbstractOperationPO) specRepos.getProofOblInput(initiatingProof);
            taclets = initiatingPO.getInitialTaclets();
        }
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof BlockExecutionPO)) {
            return false;
        }
        final BlockExecutionPO cPO = (BlockExecutionPO) po;
        return contract.equals(cPO.contract);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected String buildPOName(boolean transactionFlag) {
        return contract.getName();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected Modality getTerminationMarker() {
        return contract.getModality();
    }


    public Goal getInitiatingGoal() {
        return initiatingGoal;
    }


    public ExecutionContext getExecutionContext() {
        return context;
    }


//    public IFProofObligationVars getIFProofObligationVars() {
//        return if
//    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("Non-interference contract", contract.getUniqueName());
    }

    @Override
    public InfFlowProofSymbols getIFSymbols() {
        assert infFlowSymbols != null;
        return infFlowSymbols;
    }

    @Override
    public void addIFSymbol(JavaDLTerm t) {
        assert t != null;
        infFlowSymbols.add(t);
    }

    @Override
    public void addIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.add(n);
    }

    @Override
    public void addLabeledIFSymbol(JavaDLTerm t) {
        assert t != null;
        infFlowSymbols.addLabeled(t);
    }

    @Override
    public void addLabeledIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.addLabeled(n);
    }

    @Override
    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols) {
        assert symbols != null;
        infFlowSymbols = infFlowSymbols.unionLabeled(symbols);
    }

    @Override
    protected JavaDLTerm getGlobalDefs(LocationVariable heap,
                                 JavaDLTerm heapTerm,
                                 JavaDLTerm selfTerm,
                                 ImmutableList<JavaDLTerm> paramTerms,
                                 Services services) {
        // information flow contracts do not have global defs
        return null;
    }



    @Override
    public AbstractInfFlowPO getChildPO() {
        Proof initiatingProof = getInitiatingGoal().proof();
        Services initiatingServices = initiatingProof.getServices();
        ProofOblInput initiatingPO =
                initiatingServices.getSpecificationRepository().getProofOblInput(initiatingProof);
        assert initiatingPO instanceof AbstractInfFlowPO : "Information flow auxiliary " +
                "proof started from within non-information flow proof!?!";
        return (AbstractInfFlowPO)initiatingPO;
    }


    @Override
    public IFProofObligationVars getLeaveIFVars() {
        return getChildPO().getLeaveIFVars();
    }


    // the following code is legacy code
    @Override
    @Deprecated
    protected ImmutableList<StatementBlock> buildOperationBlocks(
                                        ImmutableList<LocationVariable> formalParVars,
                                        ProgramVariable selfVar,
                                        ProgramVariable resultVar,
                                        Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JavaDLTerm getPre(List<LocationVariable> modHeaps,
                          ProgramVariable selfVar,
                          ImmutableList<ProgramVariable> paramVars,
                          Map<LocationVariable, LocationVariable> atPreVars,
                          Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                                                "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JavaDLTerm getPost(List<LocationVariable> modHeaps,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           ProgramVariable resultVar,
                           ProgramVariable exceptionVar,
                           Map<LocationVariable, LocationVariable> atPreVars,
                           Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                                                "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JavaDLTerm buildFrameClause(List<LocationVariable> modHeaps,
                                    Map<JavaDLTerm, JavaDLTerm> heapToAtPre,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                                                "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected JavaDLTerm generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars,
                                       Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                                                "Please use the POSnippetFactory instead.");
    }
}
