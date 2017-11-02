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
import de.uka.ilkd.key.speclang.ComponentCluster;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.speclang.ServiceDependencyClusterSpec;
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
        
        //TODO JK is this the proper way to get a self var here?        
        final Term self = contract.getSelf();
        
        final ClusterSatisfactionPOFormulaFactory factory = new ClusterSatisfactionPOFormulaFactory(contract, proofServices, self);
        
        final RemoteMethodEventLDT ldt = proofServices.getTypeConverter().getRemoteMethodEventLDT();
        
        final ServiceDependencyClusterSpec localSpec = proofServices.getSpecificationRepository().getServiceDependencyClusterByLabel(contract.getSpecs().getServiceClusterLabel());
        //TODO JK make sure the specified local cluster is actually a cluster of this method?
        final EventEquivalenceWithEqFactory equivEventLocalFactory = new EventEquivalenceWithEqFactory(localSpec, self, proofConfig.getServices(), localSpec.getEquivEventEqPredicate(), localSpec.getVisibilityPredicate(), localSpec.getLabel());
        final AgreeTacletFactory agreeLocalTacletFactory = new AgreeTacletFactory(localSpec.getLowState(), proofConfig, "Local", ldt.getAgreePreLocal());
        RewriteTaclet equivEventLocalTaclet = equivEventLocalFactory.getEventEquivalenceTaclet();    
        RewriteTaclet invEventLocalTaclet = equivEventLocalFactory.getInvisibilityTaclet();
        RewriteTaclet agreeLocalTaclet = agreeLocalTacletFactory.getAgreePreTaclet();
        register(agreeLocalTaclet, proofConfig);
        register(equivEventLocalTaclet, proofConfig);
        register(invEventLocalTaclet, proofConfig);
        //TODO JK is another justification better? Reference the contract for example?
        proofConfig.registerRule(agreeLocalTaclet, AxiomJustification.INSTANCE);
        proofConfig.registerRule(equivEventLocalTaclet, AxiomJustification.INSTANCE);
        proofConfig.registerRule(invEventLocalTaclet, AxiomJustification.INSTANCE);
        

        final ComponentCluster globalSpec = proofServices.getSpecificationRepository().getComponentDependencyClusterByLabel(contract.getSpecs().getComponentClusterLabel());
        final EventEquivalenceWithEqFactory equivEventGlobalFactory = new EventEquivalenceWithEqFactory(globalSpec, self, proofConfig.getServices(), globalSpec.getEquivEventEqPredicate(), globalSpec.getVisibilityPredicate(), globalSpec.getLabel());
        final AgreeTacletFactory agreeGlobalTacletFactory = new AgreeTacletFactory(localSpec.getLowState(), proofConfig, "Global", ldt.getAgreePreGlobal());
        RewriteTaclet agreeGlobalTaclet = agreeGlobalTacletFactory.getAgreePreTaclet();
        RewriteTaclet equivEventGlobalTaclet = equivEventGlobalFactory.getEventEquivalenceTaclet();    
        RewriteTaclet invEventGlobalTaclet = equivEventGlobalFactory.getInvisibilityTaclet();  
        register(equivEventGlobalTaclet, proofConfig);
        register(invEventGlobalTaclet, proofConfig);
        register(agreeGlobalTaclet, proofConfig);
        //TODO JK is another justification better? Reference the contract for example?
        proofConfig.registerRule(equivEventGlobalTaclet, AxiomJustification.INSTANCE);
        proofConfig.registerRule(invEventGlobalTaclet, AxiomJustification.INSTANCE);
        proofConfig.registerRule(agreeGlobalTaclet, AxiomJustification.INSTANCE);
        
        
        
        
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
