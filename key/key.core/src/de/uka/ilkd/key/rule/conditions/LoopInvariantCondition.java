package de.uka.ilkd.key.rule.conditions;

import java.util.Optional;

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
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

public class LoopInvariantCondition implements VariableCondition {

    private final SchemaVariable inv;
    private final UpdateSV u;

    public LoopInvariantCondition(SchemaVariable inv, UpdateSV u) {
        this.inv = inv;
        this.u = u;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(inv) != null
                && svInst.getInstantiation(u) != null) {
            return matchCond;
        }

        final MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        final Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        final LoopStatement loop = (LoopStatement) activeStmt;
        final Term properInvInst = services.getSpecificationRepository()
                .getLoopSpec(loop).getInvariant(services);

        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loop, services);
        final Pair<Term, SVInstantiations> anons = createLocalAnonUpdate(
                localOuts, svInst, services);
        final Term anonUpdate = anons.first;
        svInst = anons.second;

        svInst = svInst.add(inv, properInvInst, services);
        svInst = svInst.add(u, anonUpdate, services);

        return matchCond.setInstantiations(svInst);
    }

    private static Pair<Term, SVInstantiations> createLocalAnonUpdate(
            ImmutableSet<ProgramVariable> localOuts, SVInstantiations svInst,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        Term anonUpdate = tb.skip();
        for (ProgramVariable pv : localOuts) {
            Function anonFunc;
            final Name svName = new Name("#" + pv.name().toString());
            final SchemaVariable existSV = svInst.lookupVar(svName);
            if (existSV != null) {
                final Term freeInst = (Term) svInst.getInstantiation(existSV);
                anonFunc = anonConstForPV(pv, Optional.of(freeInst.toString()),
                        services);
            } else {
                anonFunc = anonConstForPV(pv, Optional.empty(), services);
            }
            final Term elemUpd = tb.elementary((LocationVariable) pv,
                    tb.func(anonFunc));
            anonUpdate = tb.parallel(anonUpdate, elemUpd);
            final SchemaVariable sv = SchemaVariableFactory
                    .createSkolemTermSV(svName, pv.sort());
            svInst = svInst.add(sv, tb.func(anonFunc), services);
            svInst = svInst.makeInteresting(sv, services);
        }

        return new Pair<>(anonUpdate, svInst);
    }

    private static Function anonConstForPV(ProgramVariable pv,
            Optional<String> name, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Name anonFuncName = new Name(
                name.orElse(tb.newName(pv.name().toString())));
        final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
        services.getNamespaces().functions().addSafely(anonFunc);
        return anonFunc;
    }

    @Override
    public String toString() {
        return "\\getInvariant(" + inv + ", " + u + ")";
    }
}
