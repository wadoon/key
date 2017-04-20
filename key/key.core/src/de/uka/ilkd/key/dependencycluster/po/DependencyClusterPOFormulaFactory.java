package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.BasicSnippetData;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowInputOutputRelationSnippet;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.TempEventLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import de.uka.ilkd.key.util.DependencyClusterSpec;
import de.uka.ilkd.key.util.InfFlowSpec;

public class DependencyClusterPOFormulaFactory {
    private final DependencyClusterContract contract;
    private final IFProofObligationVars ifVars;
    private final Services services;
    private final TermBuilder tb;
    private final TempEventLDT ldt;
    private final ProofObligationVars symbExecVars;
    
    
    
    private final SymbExecWithHistFactory a;
    private final SymbExecWithHistFactory b;
    
    //TODO JK try better code reuse and remove these later
    private final InfFlowPOSnippetFactory f;
    private final InformationFlowContract infFlowContract;

    
    public DependencyClusterPOFormulaFactory(DependencyClusterContract contract, ProofObligationVars symbExecVars, IFProofObligationVars ifVars, Services services) {
        this.contract = contract;
        this.ifVars = ifVars;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.ldt = services.getTypeConverter().getTempEventLDT();
        this.symbExecVars = symbExecVars;
        
        ImmutableList<InfFlowSpec> infFlowSpecs = ImmutableSLList.<InfFlowSpec>nil();
        
        //TODO JK think about how to handle multiple clusters! Check whether all cluster specs make it to this point!
        for (DependencyClusterSpec spec: contract.getSpecs()) {
            InfFlowSpec infFlowSpec = new InfFlowSpec(spec.getLowState(), spec.getLowState(), spec.getNewObjects());
            infFlowSpecs = infFlowSpecs.append(infFlowSpec);
        }
        
        infFlowContract = 
                new InformationFlowContractImpl(contract.getName(), 
                        contract.getKJT(), 
                        contract.getTarget(), 
                        contract.getSpecifiedIn(), 
                        contract.getModality(), 
                        contract.getPre(), 
                        contract.getMby(), 
                        contract.getMod(), 
                        contract.hasModifiesClause(), 
                        contract.getSelfVar(), 
                        contract.getParams(), 
                        contract.getResult(), 
                        contract.getExc(), 
                        contract.getHeapAtPre(), 
                        contract.getDep(),
                        infFlowSpecs,
                        true);
        
        f = POSnippetFactory.getInfFlowFactory(infFlowContract, ifVars.c1, ifVars.c2, services);

        
        a = new SymbExecWithHistFactory(contract, symbExecVars, ifVars.c1, services, tb.var(ldt.getHist_A()));
        b = new SymbExecWithHistFactory(contract, symbExecVars, ifVars.c2, services, tb.var(ldt.getHist_B()));
    }
    
    public SymbExecWithHistFactory a() {
        return a;
    }
    
    public SymbExecWithHistFactory b() {
        return b;
    }
    
    public Term bothExecutions() {
        return tb.and(a.updatedExecutionWithPreAndPost(), b.updatedExecutionWithPreAndPost());
    }
    
    public Term consequence() {       
        return tb.and(postStateEquivalence(), equivalentHistories());
    }
    
    public Term assumptions() {
        return tb.and(wellformedHistories(), cooperationalEquivalence(), callEventEquivalence(), preStateEquivalence());
    }
    
    public Term preStateEquivalence() {
        InfFlowInputOutputRelationSnippet snippet = new InfFlowInputOutputRelationSnippet();
        
        BasicSnippetData d = new BasicSnippetData(infFlowContract, services);
        
        return snippet.produceInputRelation(d, ifVars.c1, ifVars.c2);
    }
    
    public Term postStateEquivalence() {
        InfFlowInputOutputRelationSnippet snippet = new InfFlowInputOutputRelationSnippet();
        
        BasicSnippetData d = new BasicSnippetData(infFlowContract, services);
        
        return snippet.produceOutputRelation(d, ifVars.c1, ifVars.c2);
    }
    
    public Term equivalentHistories() {
        return tb.func(ldt.equivHistory(), a.postHistory(), b.postHistory());
    }
    
   
    public Term wellformedHistories() {
        return tb.and(a.wellformedHistory(), b.wellformedHistory());
    }
    
    //services called with equivalent events are guaranteed to terminate with equivalent events
    public Term cooperationalEquivalence() {
        return tb.func(ldt.coopListEquiv(), a.visibilityFilteredPostHistory(), b.visibilityFilteredPostHistory());      
    }
    
    public Term callEventEquivalence() {
        return tb.func(ldt.equivEvent(), a.callEventFromPostHist(), b.callEventFromPostHist());
    }
    
    
    public Term completeFormula() {
        return tb.imp(bothExecutions(), tb.imp(assumptions(), consequence()));
    }

}
