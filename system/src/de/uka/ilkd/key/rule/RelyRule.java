package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.GuaranteePO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.speclang.ThreadSpecification;

/**
 * Rule to handle heap read access in concurrent programs
 * using rely/guarantee contracts.
 * @author bruns
 *
 */
public final class RelyRule implements BuiltInRule {

    public final static RelyRule INSTANCE = new RelyRule();
    private static final Name NAME = new Name("Rely");
    public static final String CONCURRENCY_OPTION = "concurrency";
    public static final String EXC_OPTION = "runtimeExceptions";
    private static enum ExcOption { IGNORE, ALLOW, BAN; }
    private static enum RuleType { EMPTY_MOD, FIELD_ACCESS, ARRAY_ACCESS;
        @Override
        public String toString() { return super.toString().replace('_', ' ').toLowerCase(); }
    }

    private static Term lastFocusTerm;
    private static Instantiation lastInstantiation;
    private static RuleType type;

    private static boolean relyGuaranteeEnabled(final Goal goal) {
        final String concurrencyChoice =
                goal.proof().getSettings().getChoiceSettings().getDefaultChoice(CONCURRENCY_OPTION);
        return (CONCURRENCY_OPTION + ":RG").equals(concurrencyChoice);
    }

    private static ExcOption exceptionOption(final Goal goal) {
        final String excChoice = goal.proof().getSettings().getChoiceSettings().getDefaultChoice(EXC_OPTION);
        final ExcOption res;
        if ((EXC_OPTION + ":ignore").equals(excChoice)) {
            res = ExcOption.IGNORE;
        } else if ((EXC_OPTION + ":allow").equals(excChoice)) {
            res = ExcOption.ALLOW;
        } else if ((EXC_OPTION + ":ban").equals(excChoice)) {
            res = ExcOption.BAN;
        } else {
            res = null;
            throw new RuntimeException("The setting for the RuntimeException-option is not valid: "
                                        + excChoice);
        }
        return res;
    }

    private static Term extractUpdateTarget(final Term formula) {
        if (formula != null && formula.op() instanceof UpdateApplication) {
            return UpdateApplication.getTarget(formula);
        } else {
            return formula;
        }
    }

    private static LocationVariable getTargetVar(final Proof proof) {
        final ProofOblInput po =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        final LocationVariable threadTarget =
                (po instanceof GuaranteePO) ? ((GuaranteePO) po).getTarget() : null;
        return threadTarget;
    }

    private static Term buildThreadVarUpd(final LocationVariable threadVar, final Goal g,
                                          final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term threadTarget =
                tb.dot(threadVar.sort(), tb.var(threadVar), getTargetVar(g.proof()));
        return tb.elementary(threadTarget, tb.var(threadVar));
    }

    private static Term buildAnonUpd(final Term heap,
                                     final ThreadSpecification ts,
                                     final Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Sort heapSort = heapLDT.targetSort();
        final TermBuilder tb = services.getTermBuilder();

        Term threadVar = tb.var(ts.getThreadVar());
        final Term notAssigned = ts.getNotChanged(threadVar, services);
        final Term assigned = tb.setMinus(tb.allLocs(), notAssigned);
        final Term anonHeap = tb.func(new Function(new Name("anonHeapRely"), heapSort));

        return tb.elementary(heap, tb.anon(heap, assigned, anonHeap));
    }

    private static Term buildFieldAccAssignUpd(final ProgramVariable lhs,
                                               final FieldReference fieldRef,
                                               final Term heap,
                                               final Services services) throws RuleAbortException {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        final ProgramVariable pv = fieldRef.getProgramVariable();

        Term receiver = null;
        try {
            receiver = tb.parseTerm("" + fieldRef.getReferencePrefix());
        } catch (ParserException e) {
            throw new RuleAbortException(e);
        }

        final Sort targetSort = pv.sort();
        final Term field = tb.func(heapLDT.getFieldSymbolForPV((LocationVariable)pv, services));

        return tb.elementary(tb.var(lhs), tb.select(targetSort, heap, receiver, field));
    }

    private static Term buildArrayAccAssignUpd(final ProgramVariable lhs,
                                               final ArrayReference arrayRef,
                                               final Term heap,
                                               final Term target,
                                               final Services services) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();

        Term receiver = null;
        Term idx = null;
        try {
            receiver = tb.parseTerm(""+arrayRef.getReferencePrefix());
            idx = tb.parseTerm(""+arrayRef.getDimensionExpressions().get(0));
        } catch (ParserException e) {
            throw new RuleAbortException(e);
        }

        final ExecutionContext ec = JavaTools.getInnermostExecutionContext(target.javaBlock(), services);
        final Type arrayType = arrayRef.getKeYJavaType(services, ec).getJavaType();
        assert arrayType instanceof ArrayType;
        final Sort targetSort = ((ArrayType) arrayType).getBaseType().getKeYJavaType().getSort();
        return tb.elementary(tb.var(lhs), tb.select(targetSort, heap, receiver, tb.arr(idx)));
    }

    private static ThreadSpecification searchThreadSpec(final Services services) {
        final LocationVariable targetVar = getTargetVar(services.getProof());

        for (final ProgramVariable var: ThreadSpecification.getThreads(services)) {
            final ProgramVariable target =
                    services.getJavaInfo().getAttributeSuper(GuaranteePO.TARGET, var.getKeYJavaType());
            if (target.equals(targetVar)) {
                return services.getSpecificationRepository().getThreadSpecification(var.getKeYJavaType());
            }
        }
        return null;
    }

    private static ThreadSpecification getApplicableThreadSpec(final Term target, final Services services) {
        ExecutionContext ec = JavaTools.getInnermostExecutionContext(target.javaBlock(), services);
        final TypeReference typeRef = ec != null ? ec.getThreadTypeReference() : null;
        final KeYJavaType threadType = typeRef != null ? typeRef.getKeYJavaType() : null;
        if (ec == null && target.javaBlock().size() == 0 && type == RuleType.EMPTY_MOD) {
            return searchThreadSpec(services);
        } else {
            return services.getSpecificationRepository().getThreadSpecification(threadType);
        }
    }

    private static void nullReferenceGoal(final ImmutableList<Goal> goals, final PosInOccurrence pio,
                                          final Term update, FieldReference fieldRef,
                                          final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Goal normExecGoal = goals.tail().head();
        final Goal nullRefGoal = goals.head();
        normExecGoal.setBranchLabel("Normal Execution (" + fieldRef + " != null");
        nullRefGoal.setBranchLabel("Null Reference (" + fieldRef + " = null)");
        final ProgramVariable pv = fieldRef.getProgramVariable();
        final Term eqNull = tb.equals(tb.var(pv), tb.NULL());

        nullRefGoal.addFormula(new SequentFormula(tb.apply(update, eqNull)),
                               true, true);
        nullRefGoal.changeFormula(new SequentFormula(tb.ff()), pio);
    }

    private static ImmutableList<Goal> setupFieldAccessRule(final Goal goal,
                                                            final PosInOccurrence pio,
                                                            final ExcOption exc,
                                                            final FieldReference fieldAcc,
                                                            final Term leadingUpd,
                                                            final Services services) {
        final ImmutableList<Goal> res;
        switch (exc) {
            case IGNORE:
                res = goal.split(1);
                break;
            case BAN:
                final ProgramVariable fieldAccPV = fieldAcc.getProgramVariable();
                if (fieldAccPV.isStatic() || fieldAccPV.isFinal()) {
                    res = goal.split(1);
                } else {
                    res = goal.split(2);
                    nullReferenceGoal(res, pio, leadingUpd, fieldAcc, services);
                }
                //assert false : "TODO";
                break;
            case ALLOW:
                res = goal.split(2);
                assert false : "TODO";
                break;
            default:
                res = null;
        }
        return res;
    }

    private static ImmutableList<Goal> setupArrayAccessRule(final Goal goal, final ExcOption exc) {
        final ImmutableList<Goal> res;
        switch (exc) {
            case IGNORE:
                res = goal.split(1);
                break;
            case BAN:
                res = goal.split(3);
                assert false : "TODO";
                break;
            case ALLOW:
                res = goal.split(3);
                assert false : "TODO";
                break;
            default:
                res = null;
        }
        return res;
    }

    private static void setupGeneralRely(final Goal goal, final PosInOccurrence pio,
                                         final Term newProg, final Term leadingUpd,
                                         final ThreadSpecification ts, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term heap = tb.getBaseHeap();
        final Term prevHeap = tb.getPrevHeap();

        final Term anonUpd = buildAnonUpd(heap, ts, services);
        final Term threadVarUpd = buildThreadVarUpd(ts.getThreadVar(), goal, services);
        final Term prevUpd = tb.parallel(tb.elementary(prevHeap, heap), anonUpd);

        final Term rely = ts.getRely(prevHeap, heap, tb.var(ts.getThreadVar()), services);

        if (rely != tb.tt()) {
            // add rely in any case
            final Term addRely = tb.applySequential(new Term[] {leadingUpd, prevUpd}, rely);
            goal.addFormula(new SequentFormula(addRely), true, false);
        }
        final Term prog = // new post condition
                tb.applySequential(new Term[] {leadingUpd, anonUpd, threadVarUpd}, newProg);
        goal.changeFormula(new SequentFormula(prog), pio);
    }

    private static boolean occursNotAtTopLevelInSuccedent(final PosInOccurrence occurrence) {
        return occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec();
    }

    static Instantiation getInstantiation(Term target, final Goal goal) {
        if (target == lastFocusTerm) {
            return lastInstantiation;
        }
        target = extractUpdateTarget(target); // must be applied on modality possibly with one update
        if (!(target.op() instanceof Modality)) {
            return null;
        }
        final SourceElement activeStm = JavaTools.getActiveStatement(target.javaBlock());

        if ((activeStm instanceof StatementBlock)
                && ((StatementBlock)activeStm).isEmpty()
                && target.javaBlock().size() == 0
                && target.javaBlock().program() != null) {
            return new Instantiation(target); // empty modality
        } else if (activeStm instanceof Assignment) {
            final Assignment stm = (Assignment)activeStm;
            final Expression lhs = stm.getLhs();
            final Expression rhs = stm.getRhs();

            // investigate RHS
            if (rhs instanceof FieldReference) {
                // must be field access (excludes array length)
                final FieldReference fieldRef = (FieldReference) rhs;
                final boolean isTargetVar =
                        fieldRef.getProgramVariable().equals(getTargetVar(goal.proof()));
                if (!fieldRef.getProgramVariable().isFinal() || isTargetVar) {
                    // must not be final and target variable must be treated
                    // prefix may still be this, static access (w/ variable prefix)
                    return new Instantiation(target, lhs, fieldRef); // TODO
                }
            } else if (rhs instanceof ArrayReference) {
                return new Instantiation(target, lhs, (ArrayReference) rhs);
            }
        }
        // not the empty modality
        // not an array reference
        // not a non-final field reference (except the thread target itself)
        return null;
    }

    @Override
    public boolean isApplicable(final Goal goal, final PosInOccurrence pio) {
        if (occursNotAtTopLevelInSuccedent(pio)
                || Transformer.inTransformer(pio)
                || !relyGuaranteeEnabled(goal) /* check whether rely/guarantee option is set */) {
            return false;
        }
        final Term target = pio.subTerm();
        final Instantiation inst = getInstantiation(target, goal);
        lastFocusTerm = target;
        lastInstantiation = inst;
        if (inst == null) {
            return false;
        }
        assert type != null;
        final Services services = goal.proof().getServices();
        final ThreadSpecification ts = getApplicableThreadSpec(extractUpdateTarget(target), services);
        return ts != null;
    }

    private static ImmutableList<Goal> apply(final Goal goal,
                                             final Services services,
                                             final PosInOccurrence pio,
                                             final Instantiation inst,
                                             final ThreadSpecification ts) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();
        final Term subTerm = pio.subTerm();
        final Term heap = tb.getBaseHeap();
        final ExcOption exc = exceptionOption(goal);

        // PIO is possibly an update applied to a modality
        final Term leadingUpd = (subTerm.op() instanceof UpdateApplication) ? subTerm.sub(0) : null;
        final Term target = leadingUpd == null ? subTerm : subTerm.sub(1);
        assert target == inst.target;

        final ImmutableList<Goal> res;
        final Term assignUpd; // the particular assignment effect

        switch (type) {
        case EMPTY_MOD: // empty modality rule
            res = goal.split(1);
            assignUpd = null;
            break;
        case FIELD_ACCESS: //  // field (attribute) read access
            assert inst.fieldAccess != null;
            res = setupFieldAccessRule(goal, pio, exc, inst.fieldAccess, leadingUpd, services);
            assignUpd = buildFieldAccAssignUpd(inst.lhs, inst.fieldAccess, heap, services);
            break;
        case ARRAY_ACCESS: // array read access
            assert inst.arrayAccess != null;
            res = setupArrayAccessRule(goal, exc);
            assignUpd = buildArrayAccAssignUpd(inst.lhs, inst.arrayAccess, heap, target, services);
            break;
        default:
            throw new RuleAbortException("Invalid rule instantiation!");
        }

        final Term newProg;
        final Term post = target.sub(0);
        if (assignUpd != null) {
            assert type != RuleType.EMPTY_MOD;
            final JavaBlock newBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);
            final Term prog = tb.prog((Modality)target.op(), newBlock, post);
            newProg = tb.apply(assignUpd, prog); // assignment effect in any case
        } else {
            newProg = post;
        }
        setupGeneralRely(goal, pio, newProg, leadingUpd, ts, services);
        return res;
    }

    @Override
    public ImmutableList<Goal> apply(final Goal goal,
                                     final Services services,
                                     final RuleApp ruleApp) throws RuleAbortException {
        if (!(ruleApp instanceof RelyBuiltInRuleApp)) {
            throw new RuleAbortException();
        }
        final Instantiation inst = ((RelyBuiltInRuleApp)ruleApp).inst;
        if (inst == null) {
            throw new RuleAbortException();
        }
        final ThreadSpecification ts =
                getApplicableThreadSpec(extractUpdateTarget(inst.target), services);
        if (ts == null) {
            throw new RuleAbortException();
        }
        return apply(goal, services, ruleApp.posInOccurrence(), inst, ts);
    }

    @Override
    public Name name() {
        return new Name(NAME + " (" + type + ")");
    }

    @Override
    public String displayName() {
        return name().toString();
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public IBuiltInRuleApp createApp(final PosInOccurrence pos, final TermServices services) {
        return new RelyBuiltInRuleApp(this, pos);
    }

    static class Instantiation {

        final Term target;
        final ProgramVariable lhs;
        final FieldReference fieldAccess;
        final ArrayReference arrayAccess;

        private Instantiation (final Term target) {
            assert target.javaBlock() != null;
            type = RuleType.EMPTY_MOD;
            this.target = target;
            lhs = null;
            fieldAccess = null;
            arrayAccess = null;
        }

        private Instantiation (final Term target, final Expression lhs, final FieldReference fr) {
            assert target.javaBlock() != null;
            assert lhs instanceof ProgramVariable: "unexpected: " + lhs;
            type = RuleType.FIELD_ACCESS;
            this.target = target;
            this.lhs = (ProgramVariable)lhs;
            fieldAccess = fr;
            arrayAccess = null;
        }

        private Instantiation (final Term target, final Expression lhs, final ArrayReference ar) {
            assert target.javaBlock() != null;
            assert lhs instanceof ProgramVariable: "unexpected: " + lhs;
            type = RuleType.FIELD_ACCESS;
            this.target = target;
            this.lhs = (ProgramVariable)lhs;
            fieldAccess = null;
            arrayAccess = ar;
        }
    }
}