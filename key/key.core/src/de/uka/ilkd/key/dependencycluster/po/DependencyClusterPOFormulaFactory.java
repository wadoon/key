package de.uka.ilkd.key.dependencycluster.po;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.BasicSnippetData;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowInputOutputRelationSnippet;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.ServiceEventLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import de.uka.ilkd.key.speclang.ServiceDependencyClusterSpec;
import de.uka.ilkd.key.util.InfFlowSpec;

public class DependencyClusterPOFormulaFactory {
    private final DependencyClusterContract contract;
    private final IFProofObligationVars ifVars;
    private final Services services;
    private final TermBuilder tb;
    private final ServiceEventLDT ldt;
    private final ProofObligationVars symbExecVars;
    
    
    
    private final SymbExecWithHistFactory a;
    private final SymbExecWithHistFactory b;
    
    //TODO JK try better code reuse and remove these later
    private final InformationFlowContract infFlowContract;
    
    Term internalHist_A;
    Term internalHist_B;

    
    public DependencyClusterPOFormulaFactory(DependencyClusterContract contract, ProofObligationVars symbExecVars, IFProofObligationVars ifVars, Services services) {
        this.contract = contract;
        this.ifVars = ifVars;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.ldt = services.getTypeConverter().getServiceEventLDT();
        this.symbExecVars = symbExecVars;
        
        ImmutableList<InfFlowSpec> infFlowSpecs = ImmutableSLList.<InfFlowSpec>nil();
        
        ServiceDependencyClusterSpec spec = contract.getSpecs();
        InfFlowSpec infFlowSpec = new InfFlowSpec(spec.getLowState(), spec.getLowState(), spec.getNewObjects());
        infFlowSpecs = infFlowSpecs.append(infFlowSpec);
        
        
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
        
        //TODO JK check if that stuff works with Karsten's history
        LocationVariable hist = ldt.getHist();
        Term hist_A = tb.var(new LocationVariable(new ProgramElementName(tb.newName(hist + "_A")), new KeYJavaType(hist.sort())));  
        Term hist_B = tb.var(new LocationVariable(new ProgramElementName(tb.newName(hist + "_B")), new KeYJavaType(hist.sort())));
        
        internalHist_A = tb.var(new LocationVariable(new ProgramElementName(tb.newName("internalHist_A")), new KeYJavaType(hist.sort())));  
        internalHist_B = tb.var(new LocationVariable(new ProgramElementName(tb.newName("internalHist_B")), new KeYJavaType(hist.sort())));
        
        Term call_A = tb.var(new LocationVariable(new ProgramElementName(tb.newName("call_A")), new KeYJavaType(ldt.eventSort())));  
        Term call_B = tb.var(new LocationVariable(new ProgramElementName(tb.newName("call_B")), new KeYJavaType(ldt.eventSort())));
        
        Term term_A = tb.var(new LocationVariable(new ProgramElementName(tb.newName("term_A")), new KeYJavaType(ldt.eventSort())));  
        Term term_B = tb.var(new LocationVariable(new ProgramElementName(tb.newName("term_B")), new KeYJavaType(ldt.eventSort())));
        
        a = new SymbExecWithHistFactory(contract, symbExecVars, ifVars.c1, services, hist_A, internalHist_A, call_A, term_A);
        b = new SymbExecWithHistFactory(contract, symbExecVars, ifVars.c2, services, hist_B, internalHist_B, call_B, term_B);
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
       
    public Term invisibleHistoryInternal() {
        return tb.equals(tb.func(ldt.getFilterVisible(), a.postHistoryInternal()), tb.seqEmpty());
    }
    
    //No need to handle objects in a special way here, attacker can compare objects from pre and poststate and will know whether they've changed
    public Term lowPartsOfPreAndPostEqual() {
        ImmutableList<Term> collectedTerms = ImmutableSLList.<Term>nil();
        Term updateHeapPre = tb.elementary(tb.getBaseHeap(), ifVars.c1.pre.heap);
        Term updateHeapPost = tb.elementary(tb.getBaseHeap(), ifVars.c1.post.heap);
        for (Term term: contract.getSpecs().getLowState()) {
            Term termAtPre = tb.apply(updateHeapPre, term);
            Term termAtPost = tb.apply(updateHeapPost, term);
            collectedTerms = collectedTerms.append(tb.equals(termAtPre, termAtPost));
        }
        return tb.and(collectedTerms);
    }
    
    //TODO JK make sure this is correct, but the assumption of an cooperative environment makes sure that its equivalent to the original vis preserving version to make the whole history invisible
    // This uses the variables from run A by convention
    public Term visibilityPreserving() {
        return tb.and(tb.imp(callAInvisible(), tb.and(invisibleHistoryInternal(), lowPartsOfPreAndPostEqual())), tb.equals(callAInvisible(), termAInvisible()));
    }
    
    private Term termAInvisible() {
        return tb.func(ldt.getInvEvent(), a.getTermination());
    }

    private Term callAInvisible() {
        return tb.func(ldt.getInvEvent(), a.getCall());
    }

    public Term consequence() {
        return tb.and(postStateEquivalence(), visibilityPreserving(), equivalentInternalHistories(), equivalentTerminationEvents());
    }
    
    //self is implicitly considered to be low
    public Term selfAtPreEquality() {
        return tb.and(tb.equals(ifVars.c1.pre.self, contract.getSelf()), tb.equals(ifVars.c1.pre.self, ifVars.c2.pre.self));
    }
    
    public Term selfIsActiveComp() {
        return tb.equals(contract.getSelf(), tb.getActiveComponent());
    }
    
    public Term assumptions() {
        return tb.and(wellformedHistories(), cooperationalEquivalence(), selfAtPreEquality(), selfIsActiveComp(), callEventEquivalence(), preStateEquivalence());
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
    
    public Term equivalentInternalHistories() {
        return tb.func(ldt.getEquivHistoryInternal(), a.postHistoryInternal(), b.postHistoryInternal());
    }
    
    public Term equivalentTerminationEvents() {
        return tb.func(ldt.getEquivEvent(), a.getTermination(), b.getTermination());
    }
    
   
    public Term wellformedHistories() {
        return tb.and(a.wellformedHistory(), b.wellformedHistory());
    }
    
    //services called with equivalent events are guaranteed to terminate with equivalent events
    public Term cooperationalEquivalence() {
        return tb.func(ldt.getCoopListEquivInternal(), a.postHistoryInternal(), b.postHistoryInternal());      
    }
    
    public Term callEventEquivalence() {
        return tb.func(ldt.getEquivEvent(), a.getCall(), b.getCall());
    }
    
    /*
    public Term defineInternalHistories() {
        return tb.and(
                tb.equals(internalHist_A, tb.seqSub(a.postHistory(), tb.zTerm(1), tb.add(tb.seqLen(a.postHistory()), tb.zTerm(-1)))), 
                tb.equals(internalHist_B, tb.seqSub(b.postHistory(), tb.zTerm(1), tb.add(tb.seqLen(b.postHistory()), tb.zTerm(-1)))));
    }
    */
    
    public Term completeFormula() {
        return tb.imp(bothExecutions(), tb.imp(assumptions(), consequence()));
    }

}
