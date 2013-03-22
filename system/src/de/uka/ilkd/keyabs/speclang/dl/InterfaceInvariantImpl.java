package de.uka.ilkd.keyabs.speclang.dl;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.OpReplacer;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Represents an in interface invariant specification
 */
public class InterfaceInvariantImpl implements InterfaceInvariant {

    private final String name;
    private final String displayName;
    private final KeYJavaType kjt;
    private final Term inv;
    private final ParsableVariable originalHistoryVar;


    public InterfaceInvariantImpl(String name,
                                  String displayName,
                                  KeYJavaType kjt,
                                  Term inv, ParsableVariable originalHistoryVar) {
        this.name = name;
        this.displayName = displayName;
        this.kjt = kjt;
        this.inv = inv;
        this.originalHistoryVar = originalHistoryVar;
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
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }

    public Term getOriginalInvariant() {
        return inv;
    }

    private Map<Operator, Operator> getReplaceMap(ParsableVariable historyVar,
                                                  IServices services) {
        Map<Operator, Operator> result = new LinkedHashMap<Operator, Operator>();

        result.put(originalHistoryVar, historyVar);

        return result;
    }


    public Term getInvariant(SchemaVariable historySV, IServices services) {
        final Map<Operator, Operator> replaceMap
                = getReplaceMap(historySV, services);
        final OpReplacer or = new OpReplacer(replaceMap);
        Term res = or.replace(inv);
        res = services.getTermBuilder().convertToFormula(res, services);
        return res;
    }



}
