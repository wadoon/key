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
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.LinkedHashMap;


public class ThreadSpecification implements DisplayableSpecificationElement {
    
    private final static VisibilityModifier VM = new Public();
    private final String name;
    private final String displayName;
    
    private final KeYJavaType threadType;
    private final Term rely;
    private final Term guarantee;
    private final Term assignable;
    private final Term notChanged;
    private final LocationVariable prevHeapVar, currHeapVar;
    private final ProgramVariable threadVar;
    
    public ThreadSpecification (String name, String displayName, 
                    KeYJavaType threadType,
                    Term rely, Term guarantee, Term notChanged, Term assignable,
                    LocationVariable prevHeapVar, LocationVariable currHeapVar,
                    ProgramVariable threadVar) {
        assert name != null;
        assert threadType != null;
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
        this.rely = rely;
        this.guarantee = guarantee;
        this.assignable = assignable;
        this.notChanged = notChanged;
        this.prevHeapVar = prevHeapVar;
        this.currHeapVar = currHeapVar;
        this.threadVar = threadVar;
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
        res.put(tb.var(prevHeapVar), prevHeap);
        res.put(tb.var(currHeapVar), currHeap);
        res.put(tb.var(threadVar), threadVar2);
        return res;
    }
    
    @Override
    public String toString() {
        return "rely: "+rely+"; guarantee: "+guarantee
                        +"; assignable: "+assignable
                        +"; notChanged: "+notChanged;
    }

    @Override
    public String getHTMLText(Services serv) {
        return "<html><b>rely: </b>"+LogicPrinter.quickPrintTerm(rely, serv) 
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
        // todo Auto-generated method stub
        return null;
    }

}
