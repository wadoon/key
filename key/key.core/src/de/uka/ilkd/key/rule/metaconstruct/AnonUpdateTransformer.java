package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

public class AnonUpdateTransformer extends AbstractTermTransformer {

    public AnonUpdateTransformer() {
        super(new Name("#anonUpdateTransformer"), 1, Sort.UPDATE);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {

        MethodFrame mf = JavaTools.getInnermostMethodFrame(
                svInst.getContextInstantiation().contextProgram(), services);
        Statement activeStmt = (Statement) JavaTools
                .getActiveStatement(JavaBlock.createJavaBlock(mf.getBody()));
        LoopStatement loop = (LoopStatement) activeStmt;

        LoopSpecification spec = services.getSpecificationRepository()
                .getLoopSpec(loop);
        // Term invariant = spec.getInvariant(services);

        final Map<LocationVariable, Term> atPres = spec.getInternalAtPres();
        Modality m = (Modality) term.sub(0).op(); // term.sub(0)?
        boolean transaction = (m == Modality.DIA_TRANSACTION
                || m == Modality.BOX_TRANSACTION);
        final List<LocationVariable> heapContext = HeapContext
                .getModHeaps(services, transaction);
        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(loop, services);

        // Prepare variant
        final Term variant = //
                spec.getVariant(spec.getInternalSelfTerm(), atPres, services);
        final Term variantUpdate = prepareVariant(term, variant, services);

        final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoop = //
                new LinkedHashMap<LocationVariable, Map<Term, Term>>();

        Term beforeLoopUpdate = createBeforeLoopUpdate(services, heapContext,
                localOuts, heapToBeforeLoop);

        final TermBuilder tb = services.getTermBuilder();
        // Additional Heap Terms
        Term anonUpdate = createLocalAnonUpdate(localOuts, services);

        final Map<LocationVariable, Term> mods = new LinkedHashMap<LocationVariable, Term>();
        heapContext.forEach(heap -> mods.put(heap, spec.getModifies(heap,
                spec.getInternalSelfTerm(), atPres, services)));

        for (LocationVariable heap : heapContext) {
            final AnonUpdateData tAnon = createAnonUpdate(heap, mods.get(heap),
                    spec, services);
            anonUpdate = tb.parallel(anonUpdate, tAnon.anonUpdate);
        }
        // END Additional Heap Terms

        final Term newFormula = tb.parallel(
                tb.parallel(beforeLoopUpdate, anonUpdate), variantUpdate);

        return newFormula;
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

    /**
     * Creates the variant proof obligation and update.
     * 
     * @param inst
     *            The {@link Instantiation} for this rule application.
     * @param variant
     *            The variant term as given by the loop specification.
     * @param services
     *            The {@link Services} object.
     * @return The variant proof obligation and update.
     */
    protected static Term prepareVariant(Term term, Term variant,
            TermServices services) {
        final TermBuilder tb = services.getTermBuilder();

        final ProgramElementName variantName = new ProgramElementName(
                tb.newName("variant"));
        final LocationVariable variantPV = new LocationVariable(variantName,
                Sort.ANY);
        services.getNamespaces().programVariables().addSafely(variantPV);

        final boolean dia = ((Modality) term.sub(0).op())
                .terminationSensitive();
        final Term variantUpdate = dia ? tb.elementary(variantPV, variant)
                : tb.skip();
        // final Term variantPO = dia ? tb.prec(variant, tb.var(variantPV))
        // : tb.tt();

        return variantUpdate;
    }

    /**
     * Creates an update for the anonymization of all {@link ProgramVariable}s
     * in localOuts.
     * 
     * @param localOuts
     *            The {@link ProgramVariable}s to anonymize.
     * @param services
     *            The {@link Services} object.
     * @return The anonymizing update.
     */
    protected static Term createLocalAnonUpdate(
            ImmutableSet<ProgramVariable> localOuts, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        return localOuts.stream().map(pv -> {
            final Function anonFunc = new Function(
                    new Name(tb.newName(pv.name().toString())), pv.sort(),
                    true);
            services.getNamespaces().functions().addSafely(anonFunc);

            return tb.elementary((LocationVariable) pv, tb.func(anonFunc));
        }).reduce(tb.skip(), (acc, t) -> tb.parallel(acc, t));
    }

    /**
     * Creates the "...Before_LOOP" update needed for the variant.
     * 
     * @param services
     *            The {@link Services} object.
     * @param heapContext
     *            TODO
     * @param localOuts
     *            TODO
     * @param heapToBeforeLoop
     *            TODO
     * @return The "...Before_LOOP" update needed for the variant.
     */
    protected static Term createBeforeLoopUpdate(Services services,
            final List<LocationVariable> heapContext,
            final ImmutableSet<ProgramVariable> localOuts,
            final Map<LocationVariable, Map<Term, Term>> heapToBeforeLoop) {
        final TermBuilder tb = services.getTermBuilder();
        final Namespace<IProgramVariable> progVarNS = services.getNamespaces()
                .programVariables();

        Term beforeLoopUpdate = null;
        for (LocationVariable heap : heapContext) {
            heapToBeforeLoop.put(heap, new LinkedHashMap<Term, Term>());
            final LocationVariable lv = tb.heapAtPreVar(heap + "Before_LOOP",
                    heap.sort(), true);
            progVarNS.addSafely(lv);

            final Term u = tb.elementary(lv, tb.var(heap));
            if (beforeLoopUpdate == null) {
                beforeLoopUpdate = u;
            }
            else {
                beforeLoopUpdate = tb.parallel(beforeLoopUpdate, u);
            }

            heapToBeforeLoop.get(heap).put(tb.var(heap), tb.var(lv));
        }

        for (ProgramVariable pv : localOuts) {
            final String pvBeforeLoopName = tb
                    .newName(pv.name().toString() + "Before_LOOP");
            final LocationVariable pvBeforeLoop = new LocationVariable(
                    new ProgramElementName(pvBeforeLoopName),
                    pv.getKeYJavaType());
            progVarNS.addSafely(pvBeforeLoop);
            beforeLoopUpdate = tb.parallel(beforeLoopUpdate,
                    tb.elementary(pvBeforeLoop, tb.var(pv)));
            heapToBeforeLoop
                    .get(services.getTypeConverter().getHeapLDT().getHeap())
                    .put(tb.var(pv), tb.var(pvBeforeLoop));
        }

        return beforeLoopUpdate;
    }

    /**
     * Computes the anonymizing update, the loop heap, the base heap, and the
     * anonymized heap.
     * 
     * @param heap
     *            The original heap {@link LocationVariable}.
     * @param mod
     *            The modifiers term.
     * @param inv
     *            The loop invariant.
     * @param services
     *            The {@link Services} object.
     * @return An {@link AnonUpdateData} object encapsulating the anonymizing
     *         update, the loop heap, the base heap, and the anonymized heap.
     */
    protected static AnonUpdateData createAnonUpdate(LocationVariable heap,
            Term mod, LoopSpecification inv, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Name loopHeapName = new Name(tb.newName(heap + "_After_LOOP"));
        final Function loopHeapFunc = new Function(loopHeapName,
                heapLDT.targetSort(), true);
        services.getNamespaces().functions().addSafely(loopHeapFunc);

        final Term loopHeap = tb.func(loopHeapFunc);
        final Name anonHeapName = new Name(
                tb.newName("anon_" + heap + "_LOOP"));
        final Function anonHeapFunc = new Function(anonHeapName, heap.sort());
        services.getNamespaces().functions().addSafely(anonHeapFunc);
        final Term anonHeapTerm = tb.label(tb.func(anonHeapFunc),
                ParameterlessTermLabel.ANON_HEAP_LABEL);

        // check for strictly pure loops
        final Term anonUpdate;
        if (tb.strictlyNothing().equals(mod)) {
            anonUpdate = tb.skip();
        }
        else {
            anonUpdate = tb.anonUpd(heap, mod, anonHeapTerm);
        }

        return new AnonUpdateData( //
                anonUpdate, loopHeap, //
                tb.getBaseHeap(), anonHeapTerm);
    }

    /**
     * A container containing data for the anonymizing update, that is the
     * actual update and the anonymized heap.
     */
    protected static class AnonUpdateData {
        public final Term anonUpdate, anonHeap, loopHeap, loopHeapAtPre;

        public AnonUpdateData(Term anonUpdate, Term loopHeap,
                Term loopHeapAtPre, Term anonHeap) {
            this.anonUpdate = anonUpdate;
            this.loopHeap = loopHeap;
            this.loopHeapAtPre = loopHeapAtPre;
            this.anonHeap = anonHeap;
        }
    }
}
