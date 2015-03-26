package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.SchematicFieldReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.init.GuaranteePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.ArrayComponentTypeCondition;
import de.uka.ilkd.key.rule.conditions.ArrayLengthCondition;
import de.uka.ilkd.key.rule.conditions.FinalReferenceCondition;
import de.uka.ilkd.key.rule.conditions.IsThisReference;
import de.uka.ilkd.key.rule.conditions.JavaTypeToSortCondition;
import de.uka.ilkd.key.rule.conditions.StaticReferenceCondition;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.SuccTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Thread specification for rely/gurantee as described in Daniel Bruns' thesis.
 * The specification consists of two formulas rely and guarantee
 * and two terms of type locSet assignable and notChanged.
 * The formulas are parametric in two heaps.
 * @author bruns
 * @since 2.3.7349
 */
public class ThreadSpecification implements DisplayableSpecificationElement {

    private final static VisibilityModifier VM = new Public();
    private final String name;
    private final String displayName;

    private final KeYJavaType threadType;
    private final Term pre;
    private final Term rely;
    private final Term guarantee;
    private final Term assignable;
    private final Term notChanged;
    private final LocationVariable prevHeapVar, currHeapVar;
    private final LocationVariable threadVar;
    private static ImmutableList<ProgramVariable> threads;

    public static final String CONCURRENCY_OPTION = "concurrency";
    public static final String EXC_OPTION = "runtimeExceptions";
    public static enum ExcOption { IGNORE, ALLOW, BAN; }

    public final static boolean relyGuaranteeEnabled() {
        final ChoiceSettings settings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
                //goal.proof().getSettings().getChoiceSettings();
        final String concurrencyChoice = settings.getDefaultChoice(CONCURRENCY_OPTION);
        final boolean relyOn = (CONCURRENCY_OPTION + ":RG").equals(concurrencyChoice);

        final boolean javaRules =
                ("programRules:Java").equals(settings.getDefaultChoice("programRules"));
        assert !relyOn || javaRules;

        return relyOn;
    }

    public final static ExcOption exceptionOption() {
        final String excChoice =
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoice(EXC_OPTION);
                //goal.proof().getSettings().getChoiceSettings().getDefaultChoice(EXC_OPTION);
        final ExcOption res;
        if ((EXC_OPTION + ":ignore").equals(excChoice)) {
            res = ExcOption.IGNORE;
        } else if ((EXC_OPTION + ":allow").equals(excChoice)) {
            res = ExcOption.ALLOW;
        } else if ((EXC_OPTION + ":ban").equals(excChoice)) {
            res = ExcOption.BAN;
        } else {
            throw new RuntimeException("The setting for the RuntimeException-option is not valid: "
                                       + excChoice);
        }
        return res;
    }

    private static void generateThreadSeq(Services services) {
        ImmutableList<ProgramVariable> vars = ImmutableSLList.<ProgramVariable>nil();
        for (ThreadSpecification ts : services.getSpecificationRepository().getAllThreadSpecs()) {
            vars = vars.append(ts.getThreadVar());
        }
        threads = vars;
    }

    private static SuccTaclet taclet(final String name, final String[] ruleSet,
                                     final Term find, final ImmutableList<TacletGoalTemplate> goals,
                                     final VariableCondition[] varConds,
                                     final LocationVariable threadVar,
                                     final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term exactInstance =
                tb.exactInstance(threadVar.getKeYJavaType().getSort(), tb.var(threadVar));
        final Sequent exactInstanceSeq =
                Sequent.createAnteSequent(new Semisequent(new SequentFormula(exactInstance)));

        final SuccTacletBuilder tab = new SuccTacletBuilder();
        tab.setName(MiscTools.toValidTacletName(name));
        for (final String s: ruleSet) {
            tab.addRuleSet(new RuleSet(new Name(s)));
        }
        tab.setFind(find);
        tab.setTacletGoalTemplates(goals);
        for (final VariableCondition varCond: varConds) {
            tab.addVariableCondition(varCond);
        }
        tab.setIfSequent(exactInstanceSeq);
        return tab.getSuccTaclet();
    }

    private static AntecSuccTacletGoalTemplate goal(final Term add, final Term replaceWith) {
        final Sequent addSeq;
        if (add != null) {
            addSeq = Sequent.createAnteSequent(new Semisequent(new SequentFormula(add)));
        } else {
            addSeq = Sequent.EMPTY_SEQUENT;
        }
        final Sequent replaceSeq =
                Sequent.createSuccSequent(new Semisequent(new SequentFormula(replaceWith)));

        return new AntecSuccTacletGoalTemplate(addSeq, ImmutableSLList.<Taclet>nil(), replaceSeq);
    }

    private static final ImmutableList<TacletGoalTemplate> goals(final AntecSuccTacletGoalTemplate ... ts) {
        if (ts.length == 1) { // If no branching happens, no name is needed
            ts[0] = new AntecSuccTacletGoalTemplate(ts[0].sequent(),
                                                    ImmutableSLList.<Taclet>nil(),
                                                    ts[0].replaceWith());
        }
        ImmutableList<TacletGoalTemplate> res = ImmutableSLList.<TacletGoalTemplate>nil();
        for (TacletGoalTemplate t : ts) {
            res = res.prepend(t);
        }
        return res;
    }

    private static Term buildAnonUpd(final ThreadSpecification tspec,
                                     final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        final Term notAssigned = tspec.getNotChanged(tb.var(tspec.getThreadVar()), services);

        final Term heap = tb.getBaseHeap();
        final Term assigned = tb.setMinus(tb.allLocs(), notAssigned);
        final Term anonHeap = tb.func(new Function(new Name("anonHeapRely"), heapSort));

        return tb.elementary(heap, tb.anon(heap, assigned, anonHeap));
    }

    private static Term buildFieldAccAssignUpd(final ParsableVariable lhs,
                                               final FieldReference fieldRef,
                                               final GenericSort g,
                                               final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term heap = tb.getBaseHeap();
        final Term receiver = tb.var((ParsableVariable)fieldRef.getReferencePrefix());
        final ProgramSV pv = (ProgramSV)((SchematicFieldReference)fieldRef).getReferenceSuffix();

        final Term memberPVToField =
                tb.tf().createTerm(AbstractTermTransformer.MEMBER_PV_TO_FIELD, tb.var(pv));
        return tb.elementary(tb.var(lhs), tb.select(g, heap, receiver, memberPVToField));
    }

    private static Term buildArrayAccAssignUpd(final ParsableVariable lhs,
                                               final ArrayReference arrRef,
                                               final GenericSort g,
                                               final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term heap = tb.getBaseHeap();
        final Term array = tb.var((ParsableVariable)arrRef.getReferencePrefix());
        final Term index = tb.var((ProgramSV)((ArrayReference)arrRef).getDimensionExpressions().last());

        return tb.elementary(tb.var(lhs), tb.select(g, heap, array, tb.arr(index)));
    }

    private static Term buildToArrayRefAssignUpd(final ArrayReference arrRef,
                                                 final ParsableVariable rhs,
                                                 final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term heap = tb.getBaseHeap();
        final Term array = tb.var((ParsableVariable)arrRef.getReferencePrefix());
        final Term index = tb.var((ProgramSV)((ArrayReference)arrRef).getDimensionExpressions().last());

        return tb.elementary(heap, tb.arrayStore(array, index, tb.var(rhs)));
    }

    private static AntecSuccTacletGoalTemplate relyGoal(final Term update, final Term assignUpd,
                                                        final Term replaceTerm,
                                                        final ProgramSV v,
                                                        final ThreadSpecification tspec,
                                                        final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term heap = tb.getBaseHeap();
        final Term prevHeap = tb.getPrevHeap();

        final Term anonUpd = buildAnonUpd(tspec, services);
        final Term prevUpd = tb.parallel(tb.elementary(prevHeap, heap), anonUpd);

        final Term[] upd; // update for new post condition
        if (assignUpd != null) {
            upd = new Term[] {update, anonUpd, assignUpd};
        } else {
            upd = new Term[] {update, anonUpd};
        }

        final Term rely = tspec.getRely(prevHeap, heap, tb.var(tspec.getThreadVar()), services);
        final Term addRely;
        if (rely.equalsModRenaming(tb.tt())) {
            addRely = null;
        } else { // add rely in any case
            addRely = tb.applySequential(new Term[] {update, prevUpd}, rely);
        }

        final Term replaceWith = tb.applySequential(upd, replaceTerm);
        final AntecSuccTacletGoalTemplate relyGoal = goal(addRely, replaceWith);
        if (v != null) {
            relyGoal.setName("Normal Execution (" + v.getName() + " != null)");
        }

        return relyGoal;
    }

    private static AntecSuccTacletGoalTemplate nullReferenceGoal(final Term update,
                                                                 final ProgramSV v,
                                                                 final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term varEqNull = tb.apply(update, tb.equals(tb.var(v), tb.NULL()));
        final AntecSuccTacletGoalTemplate nullRef = goal(varEqNull, tb.ff());
        nullRef.setName("Null Reference (" + v.getName() + " = null)");
        return nullRef;
    }

    private static AntecSuccTacletGoalTemplate indexOutOfBoundsGoal(final Term update,
                                                                    final ProgramSV arr,
                                                                    final ProgramSV idx,
                                                                    final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term index = tb.var(idx);
        final Term array = tb.var(arr);

        final Term varNeqNull = tb.not(tb.equals(array, tb.NULL()));
        final Term lengthLeqIdx = tb.leq(tb.dotLength(array), index);
        final Term idxLtZero = tb.lt(index, tb.zero());

        final Term indexOutOfBounds = tb.apply(update, tb.and(varNeqNull, tb.or(lengthLeqIdx, idxLtZero)));
        final AntecSuccTacletGoalTemplate outOfBounds = goal(indexOutOfBounds, tb.ff());
        outOfBounds.setName("Index Out of Bounds (" + arr.getName() + " != null, but "
                                                    + idx.getName() +" Out of Bounds!)");
        return outOfBounds;
    }

    private static AntecSuccTacletGoalTemplate arrayStoreExceptionGoal(final Term update,
                                                                       final ProgramSV arr,
                                                                       final ProgramSV idx,
                                                                       final ProgramSV rhs,
                                                                       final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term index = tb.var(idx);
        final Term array = tb.var(arr);
        final Term var = tb.var(rhs);

        final Term varNeqNull = tb.not(tb.equals(array, tb.NULL()));
        final Term idxLtLength = tb.lt(index, tb.dotLength(array));
        final Term idxGeqZero = tb.geq(tb.zero(), index);
        final Term arrStorInvalid = tb.not(tb.arrayStoreValid(array, var));

        final Term arrayStoreException =
                tb.apply(update, tb.and(varNeqNull, idxLtLength, idxGeqZero, arrStorInvalid));
        final AntecSuccTacletGoalTemplate arrayStoreExc = goal(arrayStoreException, tb.ff());
        arrayStoreExc.setName("Array Store Exception (incompatible dynamic element type of "
                              + arr.getName() + " and " + idx.getName() +")");
        return arrayStoreExc;
    }

    private static AntecSuccTacletGoalTemplate normalFieldAccGoal(final Term prog, final Term update,
                                                                  final Operator mod,
                                                                  final ProgramSV v0,
                                                                  final SchematicFieldReference vDotA,
                                                                  final GenericSort g,
                                                                  final ThreadSpecification tspec,
                                                                  final Services services) {
        final TermFactory tf = services.getTermFactory();
        final ProgramSV v = (ProgramSV)vDotA.getReferencePrefix();

        final Term fieldAccAssignUpd = buildFieldAccAssignUpd(v0, vDotA, g, services);
        final ContextStatementBlock emptyBlock = new ContextStatementBlock(new Statement[] {}, null);
        final JavaBlock emptyJb = JavaBlock.createJavaBlock(emptyBlock);
        final Term replaceTerm = tf.createTerm(mod, new Term[] {prog}, null, emptyJb);

        return relyGoal(update, fieldAccAssignUpd, replaceTerm, v, tspec, services);
    }

    private static AntecSuccTacletGoalTemplate normalToArrayRefGoal(final Term prog, final Term update,
                                                                    final Operator mod,
                                                                    final ArrayReference vSe,
                                                                    final ProgramSV se0,
                                                                    final ThreadSpecification tspec,
                                                                    final Services services) {
        final TermFactory tf = services.getTermFactory();
        final ProgramSV v = (ProgramSV)vSe.getReferencePrefix();

        final Term arrayAccAssignUpd = buildToArrayRefAssignUpd(vSe, se0, services);
        final ContextStatementBlock emptyBlock = new ContextStatementBlock(new Statement[] {}, null);
        final JavaBlock emptyJb = JavaBlock.createJavaBlock(emptyBlock);
        final Term replaceTerm = tf.createTerm(mod, new Term[] {prog}, null, emptyJb);

        return relyGoal(update, arrayAccAssignUpd, replaceTerm, v, tspec, services);
    }

    private static AntecSuccTacletGoalTemplate normalArrayAccGoal(final Term prog, final Term update,
                                                                  final Operator mod,
                                                                  final ArrayReference arrRef,
                                                                  final ProgramSV expr,
                                                                  final GenericSort g,
                                                                  final ThreadSpecification tspec,
                                                                  final Services services) {
        final TermFactory tf = services.getTermFactory();
        final ProgramSV v = (ProgramSV)arrRef.getReferencePrefix();

        final Term arrayAccAssignUpd = buildArrayAccAssignUpd(expr, arrRef, g, services);
        final ContextStatementBlock emptyBlock = new ContextStatementBlock(new Statement[] {}, null);
        final JavaBlock emptyJb = JavaBlock.createJavaBlock(emptyBlock);
        final Term replaceTerm = tf.createTerm(mod, new Term[] {prog}, null, emptyJb);

        return relyGoal(update, arrayAccAssignUpd, replaceTerm, v, tspec, services);
    }

    private static SuccTaclet createEmptyModTaclet(final String name,
                                                   final Term prog,
                                                   final Term update,
                                                   final Operator mod,
                                                   final ThreadSpecification tspec,
                                                   final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Term find = tb.tf().createTerm(mod, new Term[]{prog}, null, JavaBlock.EMPTY_JAVABLOCK);
        final Term findTerm = tb.apply(update, find);

        final AntecSuccTacletGoalTemplate goalTemp =
                relyGoal(update, null, prog, null, tspec, services);

        return taclet("rely " + name + " empty modality",
                      new String[] {"simplify_prog"},
                      findTerm, goals(goalTemp),
                      new VariableCondition[] {},
                      tspec.getThreadVar(), services);
    }

    private static ImmutableSet<SuccTaclet> createFieldAccTaclets(final String name,
                                                                  final Term prog,
                                                                  final Term update,
                                                                  final Operator mod,
                                                                  final ThreadSpecification tspec,
                                                                  final ExcOption exc,
                                                                  final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();
        ImmutableSet<SuccTaclet> res = DefaultImmutableSet.<SuccTaclet>nil();

        final ProgramSV lhs =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#v0"),
                                                      ProgramSVSort.VARIABLE, false);
        final ProgramSV v =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#v"),
                                                      ProgramSVSort.VARIABLE, false);
        final ProgramSV a =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#a"),
                                                      ProgramSVSort.VARIABLE, false);
        final GenericSort g = new GenericSort(new Name("G"));
        final SchematicFieldReference rhs = new SchematicFieldReference(a, v);

        final ContextStatementBlock fieldAccBlock =
                new ContextStatementBlock(KeYJavaASTFactory.assign(lhs, rhs), null);
        final JavaBlock jb = JavaBlock.createJavaBlock(fieldAccBlock);
        final Term findTerm =
                tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jb));

        final AntecSuccTacletGoalTemplate normalExec =
                normalFieldAccGoal(prog, update, mod, lhs, rhs, g, tspec, services);
        final AntecSuccTacletGoalTemplate nullRef = nullReferenceGoal(update, v, services);

        final ImmutableList<TacletGoalTemplate> fieldAccGoals;
        final ImmutableList<TacletGoalTemplate> fieldAccThisGoals;
        switch (exc) {
            case IGNORE:
                fieldAccGoals = goals(normalExec);
                fieldAccThisGoals = goals(normalExec);
                break;
            case BAN:
                fieldAccGoals = goals(normalExec, nullRef);
                fieldAccThisGoals = goals(normalExec);
                break;
            case ALLOW:
                // TODO
                fieldAccGoals = null;
                fieldAccThisGoals = null;
                assert false : "TODO";
                break;
            default:
                throw new RuntimeException("The setting for the RuntimeException-option is not valid: "
                                           + exc);
        }

        res = res.add(taclet("rely " + name + " field access",
                             new String[] {"simplify_prog", "simplify_prog_subset"},
                             findTerm, fieldAccGoals,
                             new VariableCondition[] { new FinalReferenceCondition(a, true),
                                                       new ArrayLengthCondition(a, true),
                                                       new StaticReferenceCondition(a, true),
                                                       new IsThisReference(v, true),
                                                       new JavaTypeToSortCondition(a, g, false)},
                             tspec.getThreadVar(), services));
        res = res.add(taclet("rely " + name + " field access_this",
                             new String[] {"simplify_prog", "simplify_prog_subset"},
                             findTerm, fieldAccThisGoals,
                             new VariableCondition[] { new FinalReferenceCondition(a, true),
                                                       new ArrayLengthCondition(a, true),
                                                       new StaticReferenceCondition(a, true),
                                                       new IsThisReference(v, false),
                                                       new JavaTypeToSortCondition(a, g, false)},
                             tspec.getThreadVar(), services));
        return res;
    }

    private static ImmutableSet<SuccTaclet> createArrayAccTaclets(final String name,
                                                                  final Term prog,
                                                                  final Term update,
                                                                  final Operator mod,
                                                                  final ThreadSpecification tspec,
                                                                  final ExcOption exc,
                                                                  final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();
        ImmutableSet<SuccTaclet> res = DefaultImmutableSet.<SuccTaclet>nil();

        final ProgramSV v =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#v"),
                                                      ProgramSVSort.VARIABLE, false);
        final ProgramSV se =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#se"),
                                                      ProgramSVSort.SIMPLEEXPRESSION, false);
        final ProgramSV expr =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#se0"),
                                                      ProgramSVSort.SIMPLEEXPRESSION, false);
        final GenericSort g = new GenericSort(new Name("G"));
        final ArrayReference arrRef = KeYJavaASTFactory.arrayFieldAccess(v, se);

        final ContextStatementBlock toArrAssignBlock =
                new ContextStatementBlock(KeYJavaASTFactory.assign(arrRef, expr), null);
        final JavaBlock jbToArr = JavaBlock.createJavaBlock(toArrAssignBlock);
        final Term findTermToArr = tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbToArr));

        final ContextStatementBlock arrToAssignBlock =
                new ContextStatementBlock(KeYJavaASTFactory.assign(expr, arrRef), null);
        final JavaBlock jbArrTo = JavaBlock.createJavaBlock(arrToAssignBlock);
        final Term findTermArrTo = tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbArrTo));

        final AntecSuccTacletGoalTemplate normalToArrExec =
                normalToArrayRefGoal(prog, update, mod, arrRef, expr, tspec, services);
        final AntecSuccTacletGoalTemplate normalArrAccExec =
                normalArrayAccGoal(prog, update, mod, arrRef, expr, g, tspec, services);

        final AntecSuccTacletGoalTemplate nullRef = nullReferenceGoal(update, v, services);
        final AntecSuccTacletGoalTemplate indexOutOfBounds = indexOutOfBoundsGoal(update, v, se, services);
        final AntecSuccTacletGoalTemplate arrayStoreException =
                arrayStoreExceptionGoal(update, v, se, expr, services);

        final ImmutableList<TacletGoalTemplate> assignToRefArrGoals;
        final ImmutableList<TacletGoalTemplate> assignToPrimArrGoals;
        final ImmutableList<TacletGoalTemplate> arrAccGoals;
        switch (exc) {
            case IGNORE:
                assignToRefArrGoals = goals(normalToArrExec);
                assignToPrimArrGoals = goals(normalToArrExec);
                arrAccGoals = goals(normalArrAccExec);
                break;
            case BAN:
                assignToRefArrGoals = goals(normalToArrExec, nullRef, indexOutOfBounds, arrayStoreException);
                assignToPrimArrGoals = goals(normalToArrExec, nullRef, indexOutOfBounds);
                arrAccGoals = goals(normalArrAccExec, nullRef, indexOutOfBounds);
                break;
            case ALLOW:
                // TODO
                assignToRefArrGoals = null;
                assignToPrimArrGoals = null;
                arrAccGoals = null;
                assert false : "TODO";
                break;
            default:
                throw new RuntimeException("The setting for the RuntimeException-option is not valid: "
                                           + exc);
        }

        res = res.add(taclet("rely " + name + " assignment to reference array",
                             new String[] {"simplify_prog", "simplify_prog_subset"},
                             findTermToArr, assignToRefArrGoals,
                             new VariableCondition[] { new ArrayComponentTypeCondition(v, true) },
                             tspec.getThreadVar(), services));
        res = res.add(taclet("rely " + name + " assignment to primitive array",
                             new String[] {"simplify_prog", "simplify_prog_subset"},
                             findTermToArr, assignToPrimArrGoals,
                             new VariableCondition[] { new ArrayComponentTypeCondition(v, false) },
                             tspec.getThreadVar(), services));
        res = res.add(taclet("rely " + name + " array access assignment",
                             new String[] {"simplify_prog", "simplify_prog_subset"},
                             findTermArrTo, arrAccGoals,
                             new VariableCondition[] { new JavaTypeToSortCondition(v, g, true) },
                             tspec.getThreadVar(), services));
        return res;
    }

    public ThreadSpecification (String name, String displayName, KeYJavaType threadType,
                                Term pre, Term rely, Term guarantee, Term notChanged, Term assignable,
                                LocationVariable prevHeapVar, LocationVariable currHeapVar,
                                LocationVariable threadVar) {
        assert name != null;
        assert threadType != null;
        assert pre != null;
        assert rely != null;
        assert guarantee != null;
        assert assignable != null;
        assert notChanged != null;
        assert prevHeapVar != null;
        assert currHeapVar != null;
        assert threadVar != null;
        this.name = name;
        this.displayName = displayName==null? name: displayName;
        this.threadType = threadType;
        this.pre = pre;
        this.rely = rely;
        this.guarantee = guarantee;
        this.assignable = assignable;
        this.notChanged = notChanged;
        this.prevHeapVar = prevHeapVar;
        this.currHeapVar = currHeapVar;
        this.threadVar = threadVar;
    }

    /**
     * Rules to handle heap read access in concurrent programs using rely/guarantee contracts.
     * @param exc The chosen option to handle runtime exceptions.
     * @param services services.
     * @return The generated  {@link Taclet}s for rely rules.
     */
    public ImmutableSet<SuccTaclet> createTaclets(final ExcOption exc, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final ThreadSpecification tspec = this;

        ImmutableSet<SuccTaclet> res;
        final String name = tspec.getKJT().getName().toLowerCase();
        final Term prog = tb.var(SchemaVariableFactory.createFormulaSV(new Name("post")));
        final Term update = tb.var(SchemaVariableFactory.createUpdateSV(new Name("#update")));
        final ModalOperatorSV mod =
                SchemaVariableFactory.createModalOperatorSV(new Name("#allmodal"), Sort.FORMULA,
                                                            DefaultImmutableSet.<Modality>nil()
                                                            .add(Modality.BOX).add(Modality.DIA));

        res = createFieldAccTaclets(name, prog, update, mod, tspec, exc, services);
        res = res.union(createArrayAccTaclets(name, prog, update, mod, tspec, exc, services));
        res = res.add(createEmptyModTaclet(name, prog, update, mod, tspec, services));
        return res;
    }

    public Term getPre (Term currHeap, Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(null, currHeap, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(pre);
    }

    public Term getRely (Term prevHeap, Term currHeap,
                         Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(prevHeap, currHeap, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(rely);
    }

    public Term getGuarantee (Term prevHeap, Term currHeap, 
                              Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(prevHeap, currHeap, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(guarantee);
    }

    public Term getAssignable(Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(null, null, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(assignable);
    }

    public Term getNotChanged(Term threadVar, Services services) {
        final Map<Term,Term> replaceMap = getReplaceMap(null, null, threadVar, services);
        final OpReplacer or = new OpReplacer(replaceMap, services.getTermFactory());
        return or.replace(notChanged);
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
        return VM;
    }

    @Override
    public KeYJavaType getKJT() {
        return threadType;
    }

    public LocationVariable getThreadVar() {
        return threadVar;
    }

    public static ImmutableList<ProgramVariable> getThreads(Services services) {
        if (threads == null) {
            generateThreadSeq(services);
        }
        return threads;
    }

    private Map<Term, Term> getReplaceMap(Term prevHeap, Term currHeap,
                                          Term threadVar2, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        Map<Term, Term> res = new LinkedHashMap<Term, Term>();
        if (prevHeap != null)
            res.put(tb.var(prevHeapVar), prevHeap);
        res.put(tb.var(currHeapVar), currHeap);
        res.put(tb.var(threadVar), threadVar2);
        return res;
    }

    @Override
    public String toString() {
        return "pre: "+pre+"; rely: "+rely+"; guarantee: "+guarantee
                        +"; assignable: "+assignable
                        +"; notChanged: "+notChanged;
    }

    @Override
    public String getHTMLText(Services serv) {
        return "<html><b>pre: </b>"+LogicPrinter.quickPrintTerm(pre, serv)
                        +"<br><b>rely: </b>"+LogicPrinter.quickPrintTerm(rely, serv) 
                        +"<br><b>guarantee: </b>"+LogicPrinter.quickPrintTerm(guarantee, serv)
                        +"<br><b>notChanged: </b>"+LogicPrinter.quickPrintTerm(notChanged, serv)
                        +"<br><b>assignable: </b>"+LogicPrinter.quickPrintTerm(assignable, serv)
                        +"</html>";
    }

    @Override
    public int id() {
        // todo Auto-generated method stub
        return 0;
    }

    @Override
    public ProofOblInput createProofObl(InitConfig copyWithServices) {
        return new GuaranteePO(copyWithServices, this);
    }

    @Override
    public boolean equals (Object o) {
        if (o instanceof ThreadSpecification) {
            final ThreadSpecification t = (ThreadSpecification) o;
            return t.threadType.equals(threadType)
                            && t.pre.equals(pre)
                            && t.rely.equals(rely)
                            && t.guarantee.equals(guarantee)
                            && t.notChanged.equals(notChanged)
                            && t.assignable.equals(assignable);
        } else return false;
    }

    @Override
    public int hashCode() {
        return 2*pre.hashCode() + 3*rely.hashCode() + 7*guarantee.hashCode()
                        + 11*notChanged.hashCode() + 13*assignable.hashCode()
                        + 17*threadType.hashCode();
    }
}