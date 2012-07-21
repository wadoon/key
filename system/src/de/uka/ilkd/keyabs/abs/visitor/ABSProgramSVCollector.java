package de.uka.ilkd.keyabs.abs.visitor;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.keyabs.abs.ABSFieldReference;
import de.uka.ilkd.keyabs.abs.ABSLocalVariableReference;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSStatementBlock;
import de.uka.ilkd.keyabs.abs.ABSVisitorImpl;
import de.uka.ilkd.keyabs.abs.CopyAssignment;
import de.uka.ilkd.keyabs.abs.ThisExpression;

public class ABSProgramSVCollector extends ABSVisitorImpl {

    private ImmutableList<SchemaVariable> result = ImmutableSLList
            .<SchemaVariable> nil();
    private SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    public ABSProgramSVCollector(ProgramElement root,
            ImmutableList<SchemaVariable> vars, SVInstantiations instantiations) {
        super(root);
        this.result = vars;
        this.instantiations = instantiations;
    }

    public ABSProgramSVCollector(ProgramElement root,
            ImmutableList<SchemaVariable> vars) {
        super(root);
        result = vars;
    }

    public ImmutableList<SchemaVariable> getSchemaVariables() {
        return result;
    }

     @Override
    public void performActionOnProgramMetaConstruct(ProgramTransformer<ABSServices> x) {
        result = result.prepend(((ProgramTransformer<ABSServices>) x)
                .neededInstantiations(instantiations));
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        result = result.prepend((SchemaVariable) x);
    }
}
