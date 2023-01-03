package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.ProgramInstantiation;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class InnerClassCondition implements VariableCondition {
    private SchemaVariable targetType = null;
    private SchemaVariable fieldAccessed;
    private TypeResolver innerType;

    public InnerClassCondition(SchemaVariable targetType, SchemaVariable fieldAcccessed, TypeResolver innerType) {
        this.targetType = targetType;
        this.fieldAccessed = fieldAcccessed;
        this.innerType = innerType;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions matchCond, Services services) {
        LocationVariable lVar = (LocationVariable) matchCond.getInstantiations().getInstantiation(fieldAccessed);
        KeYJavaType kjt = lVar.getContainerType();
        SVInstantiations inst = matchCond.getInstantiations();
        return matchCond.setInstantiations(inst.add(targetType, new TypeRef(kjt), services));
    }
}
