package de.uka.ilkd.keyabs.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractTacletSchemaVariableCollector;
import de.uka.ilkd.keyabs.abs.visitor.ABSProgramSVCollector;

public class ABSTacletSchemaVariableCollector extends
        AbstractTacletSchemaVariableCollector {

    @Override
    protected ImmutableList<SchemaVariable> collectSVInProgram(Term t,
            ImmutableList<SchemaVariable> vars) {
        ABSProgramSVCollector prgSVColl = new ABSProgramSVCollector(
                t.javaBlock().program(), vars, instantiations);
        prgSVColl.start();
        return prgSVColl.getSchemaVariables();
    }

    @Override
    protected ImmutableList<SchemaVariable> collectSVInProgram(JavaBlock jb,
            ImmutableList<SchemaVariable> vars) {

        ABSProgramSVCollector prgSVColl = new ABSProgramSVCollector(jb.program(),
                vars, instantiations);
        prgSVColl.start();
        return prgSVColl.getSchemaVariables();
    }
    
    @Override
    public void visit(Term t) {
        super.visit(t);
    }

}
