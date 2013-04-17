package de.uka.ilkd.keyabs.speclang.dl;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.OpReplacer;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 20.03.13
 * Time: 23:58
 * To change this template use File | Settings | File Templates.
 */
public class ABSClassInvariantImpl implements ABSClassInvariant {

    private final Term inv;
    private final String name;
    private final String displayname;
    private final ParsableVariable originalHistoryVar;
    private final ParsableVariable originalHeapVar;
    private final ParsableVariable originalSelfVar;
    private final String className;


    public ABSClassInvariantImpl(String name, String displayname, String className,
                                 Term inv,
                                 ParsableVariable originalHistoryVar,
                                 ParsableVariable originalHeapVar,
                                 ParsableVariable originalSelfVar) {
        this.name = name;
        this.displayname = displayname;
        this.className = className;
        this.inv = inv;
        this.originalHistoryVar = originalHistoryVar;
        this.originalHeapVar = originalHeapVar;
        this.originalSelfVar = originalSelfVar;

        assert inv.freeVars().contains((QuantifiableVariable) originalHeapVar);

    }

    @Override
    public Term getOriginalInv() {
        return inv;
    }

    @Override
    public String getClassName() {
        return className;
    }

    public ParsableVariable getOriginalSelfVar() {
        return originalSelfVar;
    }

    @Override
    public Term getInv(ParsableVariable historyVar, ParsableVariable heapVar,
                       ParsableVariable selfVar, IServices services) {
        final Map<Operator, Operator> replaceMap
                = getReplaceMap(historyVar, heapVar, selfVar, services);
        final OpReplacer or = new OpReplacer(replaceMap);
        Term res = or.replace(inv);
        res = services.getTermBuilder().convertToFormula(res, services);
        return res;
    }

    private Map<Operator, Operator> getReplaceMap(ParsableVariable historyVar,
                                                  ParsableVariable heapVar,
                                                  ParsableVariable selfVar,
                                                  IServices services) {
        Map<Operator, Operator> result = new LinkedHashMap<Operator, Operator>();

        if(selfVar != null && originalSelfVar != null) {
            assert selfVar.sort().extendsTrans(originalSelfVar.sort());
            result.put(originalSelfVar, selfVar);
        }
        result.put(originalHistoryVar, historyVar);
        result.put(originalHeapVar, heapVar);


        return result;
    }

    @Override
    public String getName() {
        return name;  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public String getDisplayName() {
        return displayname;
    }

    @Override
    public VisibilityModifier getVisibility() {
        throw new UnsupportedOperationException("There are no visibilities in ABS (everything is private)");
    }

    @Override
    public KeYJavaType getKJT() {
        throw new UnsupportedOperationException("Classes are not types in ABS.");
    }
}
