package de.uka.ilkd.key.dependencycluster.po;

import de.uka.ilkd.key.proof.init.AbstractOperationPO;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.InfFlowProofSymbols;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.TempEventLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import de.uka.ilkd.key.util.DependencyClusterSpec;
import de.uka.ilkd.key.util.InfFlowSpec;

public class DependencyClusterContractPO extends AbstractOperationPO
        implements ContractPO {
    
    private final DependencyClusterContract contract;
    
    private final ProofObligationVars symbExecVars;

    private final IFProofObligationVars ifVars;
    
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();
    
    public DependencyClusterContractPO(InitConfig initConfig, DependencyClusterContract contract) {
        super(initConfig, contract.getName());
        
        this.contract = contract;
        
        //TODO JK Christoph creates variables here and adds "information flow symbols"? Not completely sure yet what is needed and what to do with them
        final IProgramMethod pm = contract.getTarget();
        symbExecVars =
                new ProofObligationVars(pm, contract.getKJT(), environmentServices);

        assert (symbExecVars.pre.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(symbExecVars, environmentServices);
        
        
        for (Term formalParam : symbExecVars.formalParams) {
            infFlowSymbols.add(formalParam);
        }
        for (Term formalParam : ifVars.c1.formalParams) {
            infFlowSymbols.add(formalParam);
        }
        for (Term formalParam : ifVars.c2.formalParams) {
            infFlowSymbols.add(formalParam);
        }
    
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;

        final Services proofServices = postInit();  
        
        final DependencyClusterPOFormulaFactory factory = new DependencyClusterPOFormulaFactory(contract, symbExecVars, ifVars, proofServices);
    
        assignPOTerms(factory.completeFormula());
        
        collectClassAxioms(contract.getKJT(), proofConfig);

        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        tacletBuilder.setDisplayName("AAAEquivEventDef");
        tacletBuilder.setName(new Name("AAAEquivEventDef"));
        

        Sort eventSort = (Sort)proofConfig.getServices().getNamespaces().sorts().lookup("Event");
        
        //TODO JK what about rigidness and strictness values??? Is TermSV right? Or do we need another kind of SV?
        SchemaVariable e1 = SchemaVariableFactory.createTermSV(new Name("e1"), eventSort, false, false);
        SchemaVariable e2 = SchemaVariableFactory.createTermSV(new Name("e2"), eventSort, false, false);
        
        
        Term find = tb.func(proofConfig.getServices().getTypeConverter().getTempEventLDT().equivEvent(), tb.var(e1), tb.var(e2));
        Term replaceWith = tb.func(proofConfig.getServices().getTypeConverter().getTempEventLDT().equivEvent(), tb.var(e2), tb.var(e1));
        
        
        

        tacletBuilder.setFind(find);
        tacletBuilder.addGoalTerm(replaceWith);
        
        tacletBuilder.addRuleSet((RuleSet)proofConfig.ruleSetNS().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet equivEventDef = tacletBuilder.getRewriteTaclet();

        
        register(equivEventDef, proofConfig);
        //TODO JK is another justification better?
        proofConfig.registerRule(equivEventDef, AxiomJustification.INSTANCE);

        
        
        
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
    public DependencyClusterContract getContract() {
        return (DependencyClusterContract) contract;
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
    protected Modality getTerminationMarker() {
        return getContract().getModality();
    }

    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }

}
