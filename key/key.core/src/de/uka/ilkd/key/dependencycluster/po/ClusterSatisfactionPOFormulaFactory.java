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
import de.uka.ilkd.key.speclang.ClusterSatisfactionContract;

public class ClusterSatisfactionPOFormulaFactory {

    private final Services proofServices;
    private final TermBuilder tb;
    private final RemoteMethodEventLDT eventLDT;
    private final HeapLDT heapLDT;
    private final SeqLDT seqLDT;
    private final Event a;
    private final Event b;


    public ClusterSatisfactionPOFormulaFactory(
            ClusterSatisfactionContract contract, Services proofServices) {
        this.proofServices = proofServices;
        this.tb = proofServices.getTermBuilder();
        eventLDT = proofServices.getTypeConverter().getRemoteMethodEventLDT();
        heapLDT = proofServices.getTypeConverter().getHeapLDT();
        seqLDT = proofServices.getTypeConverter().getSeqLDT();
        a = new Event("_A");
        b = new Event("_B");
    }
    
    public Term premise() {
        return tb.and(wellformed());
    }
    
    public Term consequence() {
        return tb.equals(a.event(), b.event());
    }
    
    public Term wellformed() {
        return tb.and(a.wellformed(), b.wellformed());
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
    }

}
