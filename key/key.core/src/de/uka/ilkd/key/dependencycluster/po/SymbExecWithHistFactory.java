package de.uka.ilkd.key.dependencycluster.po;
//TODO JK move this to de.uka.ilkd.key.dependencycluster.po as soon as I find a way to reuse christophs code without code duplication and ugly hacks like this

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory.Snippet;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.ServiceEventLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.DependencyClusterContract;

public class SymbExecWithHistFactory {
    private final DependencyClusterContract contract;
    private final ProofObligationVars ifVars;
    private final Services services;
    private final TermBuilder tb;
    private final ServiceEventLDT ldt;
    private final ProofObligationVars symbExecVars;
    private final BasicPOSnippetFactory f;
    private final Term postHistory;
    private final Term call;
    private final Term termination;
    private final Term postHistoryInternal;
    
    public SymbExecWithHistFactory(DependencyClusterContract contract, ProofObligationVars symbExecVars, ProofObligationVars ifVars, Services services, Term postHistory, Term postHistoryInternal, Term call, Term term) {
        this.contract = contract;
        this.ifVars = ifVars;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.ldt = services.getTypeConverter().getServiceEventLDT();
        this.symbExecVars = symbExecVars;
        //TODO JK check sort of postHistory
        this.postHistory = postHistory;
        this.postHistoryInternal = postHistoryInternal;
        
        this.call = call;
        this.termination = term;
        
        //f = POSnippetFactory.getBasicFactory(contract, ifVars, services);
        //TODO JK Can I really pass "this" while I'm still in the constructor???
        f = POSnippetFactory.getBasicFactoryWithHist(contract, services, ifVars, this);
    }
    
    public Term callEvent() {
        return tb.evConst(tb.evCall(), 
                tb.getEnvironmentCaller(), 
                ifVars.pre.self, 
                tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), services)), 
                tb.seq(ifVars.pre.localVars), //TODO JK are these the right variables?
                ifVars.pre.heap);
    }
    
    public Term defineCallVar() {
        return tb.equals(call, callEvent());
    }
    
    public Term defineTermVar() {
        return tb.equals(termination, terminationEvent());
    }
    
    public Term postHistory() {
        return this.postHistory;
    }
    
    public Term postHistoryInternal() {
        return this.postHistoryInternal;
    }
    
    public Term historyWithCallEvent() {
        return tb.seqSingleton(call);
    }
    
    public Term initialHistoryEquality() {
        return tb.equals(realHistory(), historyWithCallEvent());
    }
    
    public Term initialInternalHistoryEquality() {
        return tb.equals(realHistoryInternal(), tb.seqEmpty());
    }
    
    public Term terminationEvent() {
       return tb.evConst(tb.evTerm(), 
               tb.getEnvironmentCaller(), 
               ifVars.pre.self, 
               tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), services)), 
               tb.seq(ifVars.post.result), //TODO JK are these the right variables?
               ifVars.post.heap);
    }
        
    public Term historyWithTermEvent() {
        return tb.seqConcat(realHistory(), tb.seqSingleton(termination));
    }
    
    public Term updateHistoryWithTermEvent() {
        return tb.elementary(realHistory(), historyWithTermEvent());
    }
    
    public Term updateHistoryWithCallEvent() {
        return tb.elementary(realHistory(), historyWithCallEvent());
    }
    
    public Term updateInternalHistoryWithEmptySeq() {
        return tb.elementary(realHistoryInternal(), tb.seqEmpty());
    }
    
    public Term postHistoryEquality() {
        return tb.equals(postHistory(), historyWithTermEvent());
    }
    
    public Term postInternalHistoryEquality() {
        return tb.equals(postHistoryInternal(), realHistoryInternal());
    }
    
    public Term pre() {
        final Term freePre =
                f.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre =
                f.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        return tb.and(freePre, initialHistoryEquality(), initialInternalHistoryEquality(), defineCallVar(), contractPre);
    }
    
    public Term symbolicExecutionWithPost() {
        return f.create(Snippet.SYMBOLIC_EXEC);
    }
    
    public Term updatedExecutionWithPreAndPost() {
        final Term execWithPre = tb.and(pre(), symbolicExecutionWithPost());

        final Term updateHeap = tb.elementary(tb.getBaseHeap(), ifVars.pre.heap);
                
        return tb.apply(updateHeap, tb.apply(updateHistoryWithCallEvent(), tb.apply(updateInternalHistoryWithEmptySeq(), execWithPre)));
        //return tb.apply(updateHeap, execWithPre);
    }
    
    public Term visibilityFilteredPostHistory() {
        return tb.func(ldt.getFilterVisible(), postHistory());
    }
    
    public Term visibilityFilteredInternalPostHistory() {
        return tb.func(ldt.getFilterVisible(), postHistoryInternal());
    }
  
    
    private Term realHistory() {
        /*
        //Instead of the program variable from the ldt we try this with the ghost field in main
        //return tb.var(ldt.getHist());

        Term historyField = tb.func((Function)services.getNamespaces().lookup(new Name("Main::$hist")));
        //System.out.println(historyField);
        return tb.staticDot(services.getTypeConverter().getSeqLDT().targetSort(), historyField);
        */
        return tb.getHist();
    }
    
    private Term realHistoryInternal() {
        return tb.getInternalHist();
    }
    

    public Term wellformedHistory() {
        return tb.and(tb.func(ldt.getWellformedListInternal(), postHistoryInternal()),tb.func(ldt.getWellformedListCoopInternal(), postHistoryInternal()));
    }

    public Term getCall() {
        return call;
    }

    public Term getTermination() {
        return termination;
    }
}
