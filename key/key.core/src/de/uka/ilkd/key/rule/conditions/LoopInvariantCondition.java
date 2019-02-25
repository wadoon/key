package de.uka.ilkd.key.rule.conditions;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

public class LoopInvariantCondition implements VariableCondition {

    private final SchemaVariable inv;
    private final ModalOperatorSV x;

    public LoopInvariantCondition(SchemaVariable inv, ModalOperatorSV x) {
        this.inv = inv;
        this.x = x;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {

        SVInstantiations svInst = matchCond.getInstantiations();

        final TermBuilder tb = services.getTermBuilder();
        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);

        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        ;
        LoopStatement loop = (LoopStatement) activeStmt;
        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);
        final Map<LocationVariable, Term> atPres = spec.getInternalAtPres();

        Modality m = (Modality) svInst.getInstantiation(x);
        boolean transaction = (m == Modality.DIA_TRANSACTION
                || m == Modality.BOX_TRANSACTION);
        final List<LocationVariable> heapContext = HeapContext
                .getModHeaps(services, transaction);

        final Term invTerm = mapAndConjunct(
                services, (pv -> spec.getInvariant(pv,
                        spec.getInternalSelfTerm(), atPres, services)),
                heapContext);
        final Term invFreeTerm = mapAndConjunct(
                services, (pv -> spec.getFreeInvariant(pv,
                        spec.getInternalSelfTerm(), atPres, services)),
                heapContext);

        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loop, services);

        final Term reachableOut = localOuts.stream()
                .map(pv -> tb.reachableValue(pv))
                .reduce(tb.tt(), (Term acc, Term term) -> tb.and(acc, term));

        Term t = tb.and(tb.and(invTerm, reachableOut), invFreeTerm);

        svInst = svInst.add(inv, t, services);
        return matchCond.setInstantiations(svInst);
    }

    /**
     * Creates a conjunction of {@link Term}s that are produced by fct from the
     * elements in listOfT. fct may return null when applied to a T object; in
     * this case, the result is ignored when constructing the conjunction.
     * 
     * @param services
     *            The {@link Services} object.
     * @param fct
     *            A mapping from T objects to {@link Term}s (formulas!).
     * @param listOfT
     *            A list of T objects.
     * @return A conjunction of Terms produced by fct for all elements in
     *         listOfT.
     */
    protected static <T> Term mapAndConjunct(Services services,
            java.util.function.Function<T, Term> fct, final List<T> listOfT) {
        final TermBuilder tb = services.getTermBuilder();

        // @formatter:off
        return listOfT.stream().map(t -> fct.apply(t))
                .filter(term -> term != null)
                .reduce(tb.tt(), (acc, term) -> tb.and(acc, term));
        // @formatter:on
    }

    @Override
    public String toString() {
        return "\\getInvariant(" + inv + ", " + x + ")";
    }
}
