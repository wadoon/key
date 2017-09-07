package de.uka.ilkd.key.dependencycluster.po;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.RemoteMethodEventLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.speclang.ClusterSatisfactionContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.util.DependencyClusterSpec;
import de.uka.ilkd.key.util.Lowlist;

public class ClusterSatisfactionPO extends AbstractOperationPO
        implements ContractPO {
    
    private final ClusterSatisfactionContract contract;

    public ClusterSatisfactionPO(InitConfig initConfig, ClusterSatisfactionContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
    }

    @Override
    public ClusterSatisfactionContract getContract() {
        return contract;
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;

        final Services proofServices = postInit(); 
        
        //TODO JK is this the proper way to get a self var here? Seems like overkill, take another look
        final ProofObligationVars symbExecVars =
                new ProofObligationVars(contract.getTarget(), contract.getKJT(), proofServices);
        
        final Term self = symbExecVars.pre.self;
        
        final ClusterSatisfactionPOFormulaFactory factory = new ClusterSatisfactionPOFormulaFactory(contract, proofServices, self);
        
        final RemoteMethodEventLDT ldt = proofServices.getTypeConverter().getRemoteMethodEventLDT();
        
        final DependencyClusterSpec localSpec = proofServices.getSpecificationRepository().getServiceDependencyClusterByLabel(contract.getSpecs().getServiceClusterLabel());
                
        final EventEquivalenceWithEqFactory equivEventLocalFactory = new EventEquivalenceWithEqFactory(localSpec, self, proofConfig, ldt.getEquivEventLocal(), ldt.getInvEventLocal(), "Local");
        
        assignPOTerms(factory.completeFormula());     
        
        collectClassAxioms(contract.getKJT(), proofConfig);
        
        
    }

    @Override
    public boolean implies(ProofOblInput po) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public KeYJavaType getContainerType() {
        return contract.getKJT();
    }

    @Override
    public Term getMbyAtPre() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }

    @Override
    protected boolean isTransactionApplicable() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }

    @Override
    protected ImmutableList<StatementBlock> buildOperationBlocks(
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar, ProgramVariable resultVar,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term getPre(List<LocationVariable> modHeaps,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term getPost(List<LocationVariable> modHeaps,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, ProgramVariable exceptionVar,
            Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term getGlobalDefs(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
            Map<Term, Term> heapToAtPre, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        // TODO Auto-generated method stub
        return null;
    }


    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }

    @Override
    protected Modality getTerminationMarker() {
        // TODO Auto-generated method stub
        return null;
    }


}
