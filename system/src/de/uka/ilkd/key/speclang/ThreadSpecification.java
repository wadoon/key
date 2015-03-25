package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
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
import de.uka.ilkd.key.rule.conditions.ArrayLengthCondition;
import de.uka.ilkd.key.rule.conditions.ArrayTypeCondition;
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
import de.uka.ilkd.key.util.Pair;

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
            res = null;
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
                                     final VariableCondition[] varConds) {
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
        return tab.getSuccTaclet();
    }

    private static AntecSuccTacletGoalTemplate goalTemp(final Term add,
                                                        final Term replaceWith,
                                                        final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Sequent addSeq;
        if (add != tb.tt()) {
            addSeq = Sequent.createAnteSequent(new Semisequent(new SequentFormula(add)));
        } else {
            addSeq = Sequent.EMPTY_SEQUENT;
        }
        final Sequent replaceSeq =
                Sequent.createSuccSequent(new Semisequent(new SequentFormula(replaceWith)));

        return new AntecSuccTacletGoalTemplate(addSeq, ImmutableSLList.<Taclet>nil(), replaceSeq);
    }

    private static Term buildAnonUpd(final ThreadSpecification tspec,
                                     final LocationVariable threadVar,
                                     final Services services) {
        final TermBuilder tb = services.getTermBuilder();

        final Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        final Term notAssigned = tspec.getNotChanged(tb.var(threadVar), services);

        final Term heap = tb.getBaseHeap();
        final Term assigned = tb.setMinus(tb.allLocs(), notAssigned);
        final Term anonHeap = tb.func(new Function(new Name("anonHeapRely"), heapSort));

        return tb.elementary(heap, tb.anon(heap, assigned, anonHeap));
    }

    private static Pair<Term, Term[]> setupGeneralRely(final Term leadingUpd,
                                                       final Term assignUpd,
                                                       final ThreadSpecification tspec,
                                                       final LocationVariable threadVar,
                                                       final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term heap = tb.getBaseHeap();
        final Term prevHeap = tb.getPrevHeap();

        final Term anonUpd = buildAnonUpd(tspec, threadVar, services);
        final Term prevUpd = tb.parallel(tb.elementary(prevHeap, heap), anonUpd);

        final Term rely = tspec.getRely(prevHeap, heap, tb.var(threadVar), services);

        final Term addRely;
        if (rely != tb.tt()) {
            // add rely in any case
            addRely = tb.applySequential(new Term[] {leadingUpd, prevUpd}, rely);
        } else {
            addRely = tb.tt();
        }
        // update for new post condition
        final Term[] upd;
        if (assignUpd != null) {
            upd = new Term[] {leadingUpd, anonUpd, assignUpd};
        } else {
            upd = new Term[] {leadingUpd, anonUpd};
        }
        return new Pair<Term, Term[]> (addRely, upd);
    }

    private static SuccTaclet createEmptyModTaclet(final String name,
                                                   final Term prog,
                                                   final Term update,
                                                   final Operator mod,
                                                   final ThreadSpecification tspec,
                                                   final LocationVariable threadVar,
                                                   final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();

        final Term findTerm =
                tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, JavaBlock.EMPTY_JAVABLOCK));

        final Pair<Term, Term[]> relyPost = setupGeneralRely(update, null, tspec, threadVar, services);
        final Term rely = relyPost.first;
        final Term post = tb.applySequential(relyPost.second, prog);

        final AntecSuccTacletGoalTemplate goalTemp = goalTemp(rely, post, services);

        return taclet("rely " + name + " empty modality",
                      new String[] {"simplify_prog"},
                      findTerm,
                      ImmutableSLList.<TacletGoalTemplate>nil().prepend(goalTemp),
                      new VariableCondition[] {});
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
        final Term upd = tb.elementary(tb.var(lhs), tb.select(g, heap, receiver, memberPVToField));
        return upd;
    }

    private static AntecSuccTacletGoalTemplate normalExecGoal(final Term prog, final Term update,
                                                              final Operator mod,
                                                              final ProgramSV v0,
                                                              final SchematicFieldReference vDotA,
                                                              final GenericSort g,
                                                              final ThreadSpecification tspec,
                                                              final LocationVariable threadVar,
                                                              final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();

        final ProgramSV v = (ProgramSV)vDotA.getReferencePrefix();

        final Term fieldAccAssignUpd = buildFieldAccAssignUpd(v0, vDotA, g, services);
        final Pair<Term, Term[]> relyPost =
                setupGeneralRely(update, fieldAccAssignUpd, tspec, threadVar, services);
        final Term rely = relyPost.first;
        final Term[] upd = relyPost.second;

        final JavaBlock jb2 =
                JavaBlock.createJavaBlock(new ContextStatementBlock(new Statement[] {}, null));
        final Term replaceWith =
                tb.applySequential(upd, tf.createTerm(mod, new Term[] {prog}, null, jb2));

        final AntecSuccTacletGoalTemplate normalExec = goalTemp(rely, replaceWith, services);
        normalExec.setName("Normal Execution (" + v.getName() + " != null)");
        return normalExec;
    }

    private static AntecSuccTacletGoalTemplate normalExecLengthGoal(final Term prog, final Term update,
                                                                    final Operator mod,
                                                                    final ProgramSV v0,
                                                                    final ProgramSV v,
                                                                    final ThreadSpecification tspec,
                                                                    final LocationVariable threadVar,
                                                                    final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();

        final Term fieldAccAssignUpd = tb.elementary(tb.var(v0), tb.dotLength(tb.var(v)));
        final Pair<Term, Term[]> relyPost =
                setupGeneralRely(update, fieldAccAssignUpd, tspec, threadVar, services);
        final Term rely = relyPost.first;
        final Term[] upd = relyPost.second;

        final JavaBlock jb2 =
                JavaBlock.createJavaBlock(new ContextStatementBlock(new Statement[] {}, null));
        final Term replaceWith =
                tb.applySequential(upd, tf.createTerm(mod, new Term[] {prog}, null, jb2));

        final AntecSuccTacletGoalTemplate normalExec = goalTemp(rely, replaceWith, services);
        normalExec.setName("Normal Execution (" + v.getName() + " != null)");
        return normalExec;
    }

    private static AntecSuccTacletGoalTemplate nullReferenceGoal(final Term update,
                                                                 final ProgramSV v,
                                                                 final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term varEqNull = tb.apply(update, tb.equals(tb.var(v), tb.NULL()));
        final AntecSuccTacletGoalTemplate nullRef = goalTemp(varEqNull, tb.ff(), services);
        nullRef.setName("Null Reference (" + v.getName() + " = null)");
        return nullRef;
    }

    private static ImmutableSet<SuccTaclet> createFieldAccTaclets(final String name,
                                                                  final Term prog,
                                                                  final Term update,
                                                                  final Operator mod,
                                                                  final ThreadSpecification tspec,
                                                                  final LocationVariable threadVar,
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
        final ProgramSV length =
                SchemaVariableFactory.createProgramSV(new ProgramElementName("#length"),
                                                      ProgramSVSort.ARRAYLENGTH, false);
        final GenericSort g = new GenericSort(new Name("G"));
        final SchematicFieldReference rhs = new SchematicFieldReference(a, v);
        final SchematicFieldReference rhsLength = new SchematicFieldReference(length, v);

        final JavaBlock jb =
                JavaBlock.createJavaBlock(new ContextStatementBlock(new CopyAssignment(lhs, rhs), null));
        final Term findTerm =
                tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jb));

        final JavaBlock jbLength =
                JavaBlock.createJavaBlock(new ContextStatementBlock(new CopyAssignment(lhs, rhsLength), null));
        final Term findTermLength =
                tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbLength));

        final AntecSuccTacletGoalTemplate normalExec =
                normalExecGoal(prog, update, mod, lhs, rhs, g, tspec, threadVar, services);
        final AntecSuccTacletGoalTemplate normalExecLength =
                normalExecLengthGoal(prog, update, mod, lhs, v, tspec, threadVar, services);

        final AntecSuccTacletGoalTemplate nullRef = nullReferenceGoal(update, v, services);

        res = res.add(taclet("rely " + name + " field access",
                      new String[] {"simplify_prog", "simplify_prog_subset"},
                      findTerm,
                      ImmutableSLList.<TacletGoalTemplate>nil().prepend(normalExec).prepend(nullRef),
                      new VariableCondition[] { new FinalReferenceCondition(a, true),
                                                new ArrayLengthCondition(a, true),
                                                new StaticReferenceCondition(a, true),
                                                new ArrayTypeCondition(v, true),
                                                new IsThisReference(v, true),
                                                new JavaTypeToSortCondition(a, g, false)}));
        res = res.add(taclet("rely " + name + " field access_this",
                      new String[] {"simplify_prog", "simplify_prog_subset"},
                      findTerm,
                      ImmutableSLList.<TacletGoalTemplate>nil().prepend(normalExec),
                      new VariableCondition[] { new FinalReferenceCondition(a, true),
                                                new ArrayLengthCondition(a, true),
                                                new StaticReferenceCondition(a, true),
                                                new IsThisReference(v, false),
                                                new JavaTypeToSortCondition(a, g, false)}));
        res = res.add(taclet("rely " + name + " field access_length",
                      new String[] {"simplify_prog", "simplify_prog_subset"},
                      findTermLength,
                      ImmutableSLList.<TacletGoalTemplate>nil().prepend(normalExecLength).prepend(nullRef),
                      new VariableCondition[] { new IsThisReference(v, true)}));
        return res;
    }

    private static ImmutableSet<SuccTaclet> createArrayAccTaclets(final String name,
                                                                  final Term prog,
                                                                  final Term update,
                                                                  final Operator mod,
                                                                  final ThreadSpecification tspec,
                                                                  final LocationVariable threadVar,
                                                                  final Services services) {
        ImmutableSet<SuccTaclet> res = DefaultImmutableSet.<SuccTaclet>nil();
        // TODO: taclets for array access (maybe start with javaRules.key line 2740)

        return res;
    }

    public ThreadSpecification (String name, String displayName, 
                    KeYJavaType threadType, Term pre,
                    Term rely, Term guarantee, Term notChanged, Term assignable,
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

    public ImmutableSet<SuccTaclet> createTaclets(final ExcOption exc, final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final ThreadSpecification tspec = this;
        final LocationVariable threadVar = getThreadVar();

        ImmutableSet<SuccTaclet> res = DefaultImmutableSet.<SuccTaclet>nil();
        final String name = threadType.getName().toLowerCase();;
        final Term update = tb.var(SchemaVariableFactory.createUpdateSV(new Name("#update")));
        final Term prog = tb.var(SchemaVariableFactory.createFormulaSV(new Name("post")));
        final ModalOperatorSV mod =
                SchemaVariableFactory.createModalOperatorSV(new Name("#allmodal"), Sort.FORMULA,
                                                            DefaultImmutableSet.<Modality>nil()
                                                            .add(Modality.BOX).add(Modality.DIA));
        if (exc == ExcOption.BAN) { // TODO: Other runtime exception options
            res = res.add(createEmptyModTaclet(name, prog, update, mod, tspec, threadVar, services));
            res = res.union(createFieldAccTaclets(name, prog, update, mod, tspec, threadVar, services));
            res = res.union(createArrayAccTaclets(name, prog, update, mod, tspec, threadVar, services));
        }
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