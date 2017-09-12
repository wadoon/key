package de.uka.ilkd.key.dependencycluster.po;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.RemoteMethodEventLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.ClusterSatisfactionContract;

public class ClusterSatisfactionPOFormulaFactory {

    private final ClusterSatisfactionContract contract;
    private final Services proofServices;
    private final TermBuilder tb;
    private final RemoteMethodEventLDT eventLDT;
    private final HeapLDT heapLDT;
    private final SeqLDT seqLDT;
    private final Event a;
    private final Event b;
    
    private final Term callingComp;
    private final Term self;


    public ClusterSatisfactionPOFormulaFactory(
            ClusterSatisfactionContract contract, Services proofServices, Term self) {
        this.proofServices = proofServices;
        this.tb = proofServices.getTermBuilder();
        this.contract = contract;
        eventLDT = proofServices.getTypeConverter().getRemoteMethodEventLDT();
        heapLDT = proofServices.getTypeConverter().getHeapLDT();
        seqLDT = proofServices.getTypeConverter().getSeqLDT();
        a = new Event("_A");
        b = new Event("_B");
        
        callingComp = tb.var(new LocationVariable(new ProgramElementName(tb.newName("callingComp")), new KeYJavaType(proofServices.getJavaInfo().objectSort())));
    
        this.self = self;
    }
    
    public Term selfNotNull() {
        return tb.not(tb.equals(self, tb.NULL()));
    }
    
    public Term callingCompNotNull() {
        return tb.not(tb.equals(callingComp, tb.NULL()));
    }

    public Term premise() {
        return tb.and(selfNotNull(), callingCompNotNull(), wellformed(), anon());
    }
    
    public Term globalImplLocalEvent() {
        return tb.imp(tb.func(eventLDT.getEquivEventGlobal(), a.event(), b.event()), tb.func(eventLDT.getEquivEventLocal(), a.event(), b.event()));
    }
    
    public Term globalImplLocalState() {
        return tb.imp(tb.func(eventLDT.getAgreePreGlobal(), a.heap, b.heap), tb.func(eventLDT.getAgreePreLocal(), a.heap, b.heap));
    }
    
    public Term localImplGlobalEvent() {
        return tb.imp(tb.and(tb.func(eventLDT.getEquivEventLocal(), a.event(), b.event()), 
                        a.callable(), b.callable()), 
                tb.func(eventLDT.getEquivEventGlobal(), a.event(), b.event()));
    }
    
    public Term localImplGlobalState() {
        return tb.imp(tb.and(tb.func(eventLDT.getAgreePreGlobal(), a.heap, b.heap), tb.func(eventLDT.getAgreePreLocal(), a.heap2, b.heap2)), 
                tb.func(eventLDT.getAgreePreGlobal(), a.heapPost, b.heapPost));
    }
    
    public Term consequence() {
        return tb.and(globalImplLocalEvent(), globalImplLocalState(), localImplGlobalEvent(), localImplGlobalState());
    }
    
    public Term wellformed() {
        return tb.and(a.wellformed(), b.wellformed());
    }
    
    public Term anon() {
        return tb.and(a.anon(), b.anon());
    }
    
    public Term completeFormula() {
        return tb.imp(premise(), consequence());
    }
    
    private class Event {
        public final Term caller;
        public final Term callee;
        public final Term service;
        public final Term type;
        public final Term params;
        public final Term heap;
        public final Term heap2;
        public final Term heapPost;
        
        public Event(String varsuffix) {
            
            caller = tb.var(new LocationVariable(new ProgramElementName(tb.newName("caller" + varsuffix)), new KeYJavaType(proofServices.getJavaInfo().objectSort())));
            callee = tb.var(new LocationVariable(new ProgramElementName(tb.newName("callee" + varsuffix)), new KeYJavaType(proofServices.getJavaInfo().objectSort())));
            
            service = tb.var(new LocationVariable(new ProgramElementName(tb.newName("service" + varsuffix)), new KeYJavaType(eventLDT.getMethodSort())));
            
            type = tb.var(new LocationVariable(new ProgramElementName(tb.newName("type" + varsuffix)), new KeYJavaType(eventLDT.getCalltypeSort())));
            
            params = tb.var(new LocationVariable(new ProgramElementName(tb.newName("params" + varsuffix)), new KeYJavaType(seqLDT.targetSort())));

            heap = tb.var(new LocationVariable(new ProgramElementName(tb.newName("heap" + varsuffix)), new KeYJavaType(heapLDT.targetSort())));
            heap2 = tb.var(new LocationVariable(new ProgramElementName(tb.newName("heap2" + varsuffix)), new KeYJavaType(heapLDT.targetSort())));
            heapPost = tb.var(new LocationVariable(new ProgramElementName(tb.newName("heapPost" + varsuffix)), new KeYJavaType(heapLDT.targetSort())));
        }
        
        public Term event() {
            return tb.func(eventLDT.eventConstructor(), type, caller, callee, service, params, heap);
        }
        
        public Term wellformed() {
            return tb.and(wellformedCaller(), wellformedCallee(), wellformedHeaps());
        }

        private Term wellformedHeaps() {
            Term h = tb.wellFormed(heap);
            Term h2 = tb.wellFormed(heap2);
            Term hp = tb.wellFormed(heapPost);
            return tb.and(h, h2, hp);
        }

        public Term wellformedCallee() {
            return tb.not(tb.equals(callee, tb.NULL()));
        }

        public Term wellformedCaller() {
            return tb.not(tb.equals(caller, tb.NULL()));
        }
        
        public Term anon() {
            Term mod = contract.getMod();
            return tb.equals(heapPost, tb.anon(heap2, mod, heap));
        }
        
        public Term callable() {
            return tb.func(eventLDT.getIsCallable(), event());
        }
    }

}
