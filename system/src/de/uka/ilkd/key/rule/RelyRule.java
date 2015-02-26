package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
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

    private Term lastFocusTerm;
    private Instantiation lastInstantiation;

    private static boolean relyGuaranteeEnabled(Goal goal) {
        final String concurrencyChoice =
                goal.proof().getSettings().getChoiceSettings().getDefaultChoice(CONCURRENCY_OPTION);
        return (CONCURRENCY_OPTION + ":RG").equals(concurrencyChoice);
    }

    private static Term extractUpdateTarget(Term formula) {
        if (formula != null && formula.op() instanceof UpdateApplication) {
            return UpdateApplication.getTarget(formula);
        } else {
            return formula;
        }
    }

    private static Term buildAnonUpd(Term heap,
                                     ThreadSpecification ts,
                                     Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Sort heapSort = heapLDT.targetSort();
        final TermBuilder tb = services.getTermBuilder();

        Term threadVar = tb.var(ts.getThreadVar());
        final Term notAssigned = ts.getNotChanged(threadVar, services);
        final Term assigned = tb.setMinus(tb.allLocs(), notAssigned);
        final Term anonHeap = tb.func(new Function(new Name("anonHeapRely"), heapSort));

        return tb.elementary(heap, tb.anon(heap, assigned, anonHeap));
    }

    private static Term buildFieldAccAssignUpd(Term lhs, FieldReference fieldRef,
                                               Term heap, Services services) throws RuleAbortException {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

        Term receiver = null;
        try {
            receiver = tb.parseTerm("" + fieldRef.getReferencePrefix());
        } catch (ParserException e) {
            throw new RuleAbortException(e);
        }

        final Sort targetSort = fieldRef.getProgramVariable().sort();
        final Term field =
                tb.func(heapLDT.getFieldSymbolForPV(
                            (LocationVariable)fieldRef.getProgramVariable(),
                            services));

        return tb.elementary(lhs, tb.select(targetSort, heap, receiver, field));
    }

    private static Term buildArrayAccAssignUpd(Term lhs, ArrayReference arrayRef,
                                               Term heap, Term target,
                                               Services services) throws RuleAbortException {
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
        return tb.elementary(lhs, tb.select(targetSort, heap, receiver, tb.arr(idx)));
    }

	Instantiation getInstantiation(Term target, Goal goal) {
		// must be applied on modality possibly with one update
		target = extractUpdateTarget(target);
        if (target == lastFocusTerm) return lastInstantiation;

        if (!(target.op() instanceof Modality)) return null;
        final JavaBlock prog = target.javaBlock();
        final SourceElement activeStm = JavaTools.getActiveStatement(prog);
        if (activeStm == null) {
            // empty modality
            return new Instantiation(target);
        }
        if (!(activeStm instanceof Assignment)) return null;
        final Expression lhs = ((Assignment) activeStm).getLhs();

        // investigate RHS
        final Expression rhs = ((Assignment) activeStm).getRhs();
        // must be field access (excludes array length)
        if (rhs instanceof FieldReference) {
            assert lhs instanceof ProgramVariable: "unexpected: "+lhs;
            final ProgramVariable field = ((FieldReference) rhs).getProgramVariable();
            // must not be final
            if (field.isFinal()) return null;

            // prefix may still be this, static access (w/ variable prefix)
            return new Instantiation(target, (ProgramVariable) lhs, (FieldReference) rhs); // TODO
        } else if (rhs instanceof ArrayReference) {
            assert lhs instanceof ProgramVariable: "unexpected: "+lhs;
            return new Instantiation(target, (ProgramVariable) lhs, (ArrayReference) rhs);
        } else
            return null;
    }

	private static ThreadSpecification getApplicableThreadSpec(Term target, Services services) {
		final ExecutionContext ec =
				JavaTools.getInnermostExecutionContext(target.javaBlock(), services);
		final TypeReference typeRef = ec.getThreadTypeReference();
		final KeYJavaType threadType = typeRef != null ? typeRef.getKeYJavaType() : null;
		return services.getSpecificationRepository().getThreadSpecification(threadType);
	}

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null
                || pio.isInAntec()
                || !pio.isTopLevel()
                || Transformer.inTransformer(pio)) {
            return false;
        }
        if (!relyGuaranteeEnabled(goal)) {
            // check whether rely/guarantee option is set
            return false;
        }
        final Term target = extractUpdateTarget(pio.subTerm());
        final Instantiation inst = getInstantiation(target, goal);
        lastFocusTerm = target;
        lastInstantiation = inst;
        if (inst == null) {
            return false;
        }
        final Services services = goal.proof().getServices();
        return getApplicableThreadSpec(inst.target, services) != null;
    }

	@Override
	public ImmutableList<Goal> apply(Goal goal,
									 final Services services,
									 final RuleApp ruleApp) throws RuleAbortException {
		if (!(ruleApp instanceof RelyBuiltInRuleApp)) {
			throw new RuleAbortException();
		}
		final RelyBuiltInRuleApp app = (RelyBuiltInRuleApp) ruleApp;

		final Instantiation inst = app.inst;
		if (inst == null) {
			throw new RuleAbortException();
		}
		final ThreadSpecification ts = getApplicableThreadSpec(inst.target, services);
		if (ts == null) {
			throw new RuleAbortException();
		}
		return apply(goal, services, app.posInOccurrence(), inst, ts);
	}

	private ImmutableList<Goal> apply(Goal goal,
									  final Services services,
									  final PosInOccurrence pio,
									  final Instantiation inst,
									  final ThreadSpecification ts) throws RuleAbortException {
		final TermBuilder tb = services.getTermBuilder();
		final Term subTerm = pio.subTerm();
		final Term heap = tb.getBaseHeap();
		final Term prevHeap = tb.getPrevHeap();

		final String excChoice = goal.proof().getSettings().getChoiceSettings().getDefaultChoice(EXC_OPTION);
		final boolean ignoreRTE = (EXC_OPTION + ":ignore").equals(excChoice);
		final boolean allowRTE = (EXC_OPTION + ":allow").equals(excChoice);
		final boolean banRTE = (EXC_OPTION + ":ban").equals(excChoice);
		assert ignoreRTE || allowRTE || banRTE;

		final Term rely = ts.getRely(prevHeap, heap, tb.var(ts.getThreadVar()), services);

		// PIO is possibly an update applied to a modality
		final Term leadingUpd = (subTerm.op() instanceof UpdateApplication) ? subTerm.sub(0) : null;
		final Term target = leadingUpd == null ? subTerm : subTerm.sub(1);
		assert target == inst.target;

		final Term anonUpd = buildAnonUpd(heap, ts, services);
		final Term prevUpd = tb.parallel(tb.elementary(prevHeap, heap), anonUpd);
		final Term addRely = tb.apply(leadingUpd, tb.apply(prevUpd, rely));

		final Term post = target.sub(0);
		final ImmutableList<Goal> res;
		final Term newProg;

		if (inst.emptyMod) { // empty modality rule
			newProg = post;
			res = goal.split(1);
		} else { // read access
			final JavaBlock newBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);
			final Term prog = tb.prog((Modality)target.op(), newBlock, post);
			final Term lhs = tb.var(inst.lhs);
			final Term assignUpd; // the particular assignment effect

			if (inst.fieldAccess != null) {
				// field (attribute) access
				if (ignoreRTE) {
					res = goal.split(1);
				} else {
					// ban or allow RTE
					res = goal.split(2);
					assert false : "TODO";
				}
				assignUpd = buildFieldAccAssignUpd(lhs, inst.fieldAccess, heap, services);
			} else {
				assert (inst.arrayAccess != null);
				// array access
				if (ignoreRTE) {
					res = goal.split(1);
				} else { // ban or allow RTE
					res = goal.split(3);
					assert false : "TODO";
				}
				assignUpd = buildArrayAccAssignUpd(lhs, inst.arrayAccess, heap, target, services);
			}
			// assignment effect in any case
			newProg = tb.apply(assignUpd, prog);
		}

		// add rely in any case
		final Goal g = res.head();
		g.addFormula(new SequentFormula(addRely), true, false);
		final Term prog = tb.apply(leadingUpd, tb.apply(anonUpd, newProg)); // new post condition
		g.changeFormula(new SequentFormula(prog), pio);
		return res;
	}

    @Override
    public Name name() {
        return NAME;
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
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new RelyBuiltInRuleApp(this, pos);
    }

    static class Instantiation {

        final Term target;
        final boolean emptyMod;
        final ProgramVariable lhs;
        final FieldReference fieldAccess;
        final ArrayReference arrayAccess;

        private Instantiation (Term target) {
            this.target = target;
            assert target.javaBlock() != null;
            emptyMod = true;
            lhs = null;
            fieldAccess = null;
            arrayAccess = null;
        }

        private Instantiation (Term target, ProgramVariable lhs, FieldReference fr) {
            this.target = target;
            assert target.javaBlock() != null;
            emptyMod = false;
            this.lhs = lhs;
            fieldAccess = fr;
            arrayAccess = null;
        }

        private Instantiation (Term target, ProgramVariable lhs, ArrayReference ar) {
            this.target = target;
            assert target.javaBlock() != null;
            emptyMod = false;
            this.lhs = lhs;
            fieldAccess = null;
            arrayAccess = ar;
        }
    }
}