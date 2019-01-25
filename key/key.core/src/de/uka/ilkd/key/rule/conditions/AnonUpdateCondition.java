package de.uka.ilkd.key.rule.conditions;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

public class AnonUpdateCondition implements VariableCondition {

    private final UpdateSV u;

    public AnonUpdateCondition(UpdateSV u) {
        this.u = u;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {

        SVInstantiations svInst = matchCond.getInstantiations();

        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        LoopStatement loop = (LoopStatement) activeStmt;

        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loop, services);
        Term anonUpdate = createLocalAnonUpdate(localOuts, services);

        svInst = svInst.add(u, anonUpdate, services);
        return matchCond.setInstantiations(svInst);
    }

    private static Term createLocalAnonUpdate(
            ImmutableSet<ProgramVariable> localOuts, Services services) {
        Term anonUpdate = null;
        final TermBuilder tb = services.getTermBuilder();
        for (ProgramVariable pv : localOuts) {
            final Name anonFuncName = new Name(
                    tb.newName(pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(),
                    true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary((LocationVariable) pv,
                    tb.func(anonFunc));
            if (anonUpdate == null) {
                anonUpdate = elemUpd;
            }
            else {
                anonUpdate = tb.parallel(anonUpdate, elemUpd);
            }
        }
        return anonUpdate;
    }

    @Override
    public String toString() {
        return "\\getAnonUpdate(" + u + ")";
    }
}
