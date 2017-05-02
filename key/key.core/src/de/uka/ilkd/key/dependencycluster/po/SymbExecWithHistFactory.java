package de.uka.ilkd.key.dependencycluster.po;
//TODO JK move this to de.uka.ilkd.key.dependencycluster.po as soon as I find a way to reuse christophs code without code duplication and ugly hacks like this

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory.Snippet;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.TempEventLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.DependencyClusterContract;

public class SymbExecWithHistFactory {
    private final DependencyClusterContract contract;
    private final ProofObligationVars ifVars;
    private final Services services;
    private final TermBuilder tb;
    private final TempEventLDT ldt;
    private final ProofObligationVars symbExecVars;
    private final BasicPOSnippetFactory f;
    private final Term postHistory;
    
    public SymbExecWithHistFactory(DependencyClusterContract contract, ProofObligationVars symbExecVars, ProofObligationVars ifVars, Services services, Term postHistory) {
        this.contract = contract;
        this.ifVars = ifVars;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.ldt = services.getTypeConverter().getTempEventLDT();
        this.symbExecVars = symbExecVars;
        //TODO JK check sort of postHistory
        this.postHistory = postHistory;
        
        //f = POSnippetFactory.getBasicFactory(contract, ifVars, services);
        //TODO JK Can I really pass "this" while I'm still in the constructor???
        f = POSnippetFactory.getBasicFactoryWithHist(contract, services, ifVars, this);
    }
    
    public Term callEvent() {
        return tb.func(ldt.evConst(), 
                tb.func(ldt.evCall()), 
                tb.func(ldt.evIncoming()), 
                tb.var(ldt.getEnvironmentCaller()),
                tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), services)),
                tb.seq(ifVars.pre.localVars), //TODO JK falsche variable
                ifVars.pre.heap);
    }
    
    public Term postHistory() {
        return this.postHistory;
    }
    
    public Term historyWithCallEvent() {
        return tb.seqSingleton(callEvent());
    }
    
    public Term updateHistoryWithCallEvent() {
        return tb.elementary(realHistory(), historyWithCallEvent());
    }
    
    public Term initialHistoryEquality() {
        return tb.equals(realHistory(), historyWithCallEvent());
    }
    
    public Term terminationEvent() {
       return tb.func(ldt.evConst(), 
                tb.func(ldt.evTerm()), 
                tb.func(ldt.evOutgoing()), 
                tb.var(ldt.getEnvironmentCaller()),
                tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), services)),
                tb.seq(ifVars.post.result), 
                ifVars.post.heap);    
    }
        
    public Term historyWithTermEvent() {
        return tb.seqConcat(realHistory(), tb.seqSingleton(terminationEvent()));
    }
    
    public Term updateHistoryWithTermEvent() {
        return tb.elementary(realHistory(), historyWithTermEvent());
    }
    
    public Term postHistoryEquality() {
        return tb.equals(postHistory(), historyWithTermEvent());
    }
    
    public Term pre() {
        final Term freePre =
                f.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre =
                f.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        return tb.and(freePre, initialHistoryEquality(), contractPre);
    }
    
    public Term symbolicExecutionWithPost() {
        return f.create(Snippet.SYMBOLIC_EXEC);
    }
    
    public Term updatedExecutionWithPreAndPost() {
        final Term execWithPre = tb.and(pre(), symbolicExecutionWithPost());

        final Term updateHeap = tb.elementary(tb.getBaseHeap(), ifVars.pre.heap);
        
        return tb.apply(updateHeap, tb.apply(updateHistoryWithCallEvent(), execWithPre));
    }
    
    public Term visibilityFilteredPostHistory() {
        return tb.func(ldt.filterVisible(), postHistory());
    }
    
    public Term callEventFromPostHist() {
        //TODO JK how to get the event sort properly?
        return tb.seqGet(callEvent().sort(), postHistory(), tb.zero());
    }
    
    
    private Term realHistory() {
        return tb.var(ldt.getHist());
    }
    

    public Term wellformedHistory() {
        return tb.and(tb.func(ldt.wellformedList(), postHistory()),tb.func(ldt.wellformedListCoop(), postHistory()));
    }
}
