package de.uka.ilkd.key.speclang;

import java.util.Map;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.GuaranteePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.LinkedHashMap;

/**
 * Thread specification for rely/gurantee as described in Daniel Bruns' thesis.
 * The specification consists of two formulas rely and guarantee
 * and two terms of type locSet assignable and notChanged.
 * The formulas are parametric in two heaps.
 * @author bruns
 * @since 2.3.7349
 */
public class ThreadSpecification implements DisplayableSpecificationElement {
    
    private final static VisibilityModifier VM = new Public();
    private final String name;
    private final String displayName;
    
    private final KeYJavaType threadType;
    private final Term pre;
    private final Term rely;
    private final Term guarantee;
    private final Term assignable;
    private final Term notChanged;
    private final LocationVariable prevHeapVar, currHeapVar;
    private final ProgramVariable threadVar;
    
    public ThreadSpecification (String name, String displayName, 
                    KeYJavaType threadType, Term pre,
                    Term rely, Term guarantee, Term notChanged, Term assignable,
                    LocationVariable prevHeapVar, LocationVariable currHeapVar,
                    ProgramVariable threadVar) {
        assert name != null;
        assert threadType != null;
        assert pre != null;
        assert rely != null;
        assert guarantee != null;
        assert assignable != null;
        assert notChanged != null;
        assert prevHeapVar != null;
        assert currHeapVar != null;
        assert threadVar != null;
        this.name = name;
        this.displayName = displayName==null? name: displayName;
        this.threadType = threadType;
        this.pre = pre;
        this.rely = rely;
        this.guarantee = guarantee;
        this.assignable = assignable;
        this.notChanged = notChanged;
        this.prevHeapVar = prevHeapVar;
        this.currHeapVar = currHeapVar;
        this.threadVar = threadVar;
    }
    
    public Term getPre (Term currHeap, Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(null, currHeap, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(pre);
    }
        
    public Term getRely (Term prevHeap, Term currHeap, 
                    Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(prevHeap, currHeap, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(rely);
    }
    
    public Term getGuarantee (Term prevHeap, Term currHeap, 
                    Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(prevHeap, currHeap, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(guarantee);
    }
    
    public Term getAssignable(Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(null, null, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(assignable);
    }
    
    public Term getNotChanged(Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(null, null, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(notChanged);
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public String getDisplayName() {
        return displayName;
    }

    @Override
    public VisibilityModifier getVisibility() {
        return VM;
    }

    @Override
    public KeYJavaType getKJT() {
        return threadType;
    }

    
    private Map<Term, Term> getReplaceMap(Term prevHeap, Term currHeap,
                    Term threadVar2, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        Map<Term, Term> res = new LinkedHashMap<Term, Term>();
        if (prevHeap != null)
            res.put(tb.var(prevHeapVar), prevHeap);
        res.put(tb.var(currHeapVar), currHeap);
        res.put(tb.var(threadVar), threadVar2);
        return res;
    }
    
    @Override
    public String toString() {
        return "pre: "+pre+"; rely: "+rely+"; guarantee: "+guarantee
                        +"; assignable: "+assignable
                        +"; notChanged: "+notChanged;
    }

    @Override
    public String getHTMLText(Services serv) {
        return "<html><b>pre: </b>"+LogicPrinter.quickPrintTerm(pre, serv)
                        +"<br><b>rely: </b>"+LogicPrinter.quickPrintTerm(rely, serv) 
                        +"<br><b>guarantee: </b>"+LogicPrinter.quickPrintTerm(guarantee, serv)
                        +"<br><b>notChanged: </b>"+LogicPrinter.quickPrintTerm(notChanged, serv)
                        +"<br><b>assignable: </b>"+LogicPrinter.quickPrintTerm(assignable, serv)
                        +"</html>";
    }

    @Override
    public int id() {
        // todo Auto-generated method stub
        return 0;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig copyWithServices) {
        return new GuaranteePO(copyWithServices, this);
    }
    
    @Override
    public boolean equals (Object o) {
        if (o instanceof ThreadSpecification) {
            final ThreadSpecification t = (ThreadSpecification) o;
            return t.threadType.equals(threadType)
                            && t.pre.equals(pre)
                            && t.rely.equals(rely)
                            && t.guarantee.equals(guarantee)
                            && t.notChanged.equals(notChanged)
                            && t.assignable.equals(assignable);
        } else return false;
    }
    
    @Override
    public int hashCode() {
        return 2*pre.hashCode() + 3*rely.hashCode() + 7*guarantee.hashCode()
                        + 11*notChanged.hashCode() + 13*assignable.hashCode()
                        + 17*threadType.hashCode();
    }

}
