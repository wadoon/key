package de.uka.ilkd.key.speclang;

import java.util.Map;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.SchematicFieldReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.ldt.SeqLDT;
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
import de.uka.ilkd.key.pp.NotationInfo;
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

    /**
     * If a method is strictly pure, it has no modifies clause which could
     * be anonymised.
     * @see #hasModifiesClause()
     */
    final boolean hasMod;

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

    public ThreadSpecification (String name, String displayName, KeYJavaType threadType,
                                Term pre, Term rely, Term guarantee, Term notChanged, Term assignable,
                                boolean hasRealMod, LocationVariable prevHeapVar,
                                LocationVariable currHeapVar, LocationVariable threadVar) {
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
        this.hasMod = hasRealMod;
        this.notChanged = notChanged;
        this.prevHeapVar = prevHeapVar;
        this.currHeapVar = currHeapVar;
        this.threadVar = threadVar;
}

    private static void generateThreadSeq(Services services) {
        ImmutableList<ProgramVariable> vars = ImmutableSLList.<ProgramVariable>nil();
        for (ThreadSpecification ts : services.getSpecificationRepository().getAllThreadSpecs()) {
            vars = vars.append(ts.getThreadVar());
        }
        threads = vars;
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

        final String name = tspec.getKJT().getFullName();
        final Term prog = tb.var(SchemaVariableFactory.createFormulaSV(new Name("post")));
        final Term update = tb.var(SchemaVariableFactory.createUpdateSV(new Name("#update")));
        final ModalOperatorSV mod =
                SchemaVariableFactory.createModalOperatorSV(new Name("#allmodal"), Sort.FORMULA,
                                                            DefaultImmutableSet.<Modality>nil()
                                                            .add(Modality.BOX).add(Modality.DIA));
        final ImmutableSet<SuccTaclet> t1 = // with leading update
                TacletGenerator.createTaclets(name, prog, update, mod, tspec, exc, services);
        final ImmutableSet<SuccTaclet> t2 = // without leading update
                TacletGenerator.createTaclets(name, prog, null, mod, tspec, exc, services);
        return t1.union(t2);
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

    /**
     * Returns <code>true</code> iff the thread (according to the contract) does
     * not modify the heap at all, i.e., iff it is "strictly pure."
     *
     * @return whether this contract is strictly pure.
     */
    public boolean hasModifiesClause() {
        return hasMod;
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

    /**
     * Return String to display contract in proof management dialog
     * @param includeHtmlMarkup
     * @param services
     * @return String to display
     */
    private String getText(boolean includeHtmlMarkup, Services serv,
                           boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        final String start = includeHtmlMarkup ? "<html>" : "";
        final String startb = includeHtmlMarkup ? "<b>" : "";
        final String br = includeHtmlMarkup ? "<br>" : "\n";
        final String endb = includeHtmlMarkup ? " </b>" : " ";
        final String end = includeHtmlMarkup ? "</html>" : "";
        Map<String, Term> terms = new LinkedHashMap<String, Term>();
        terms.put("pre", pre);
        terms.put("rely", rely);
        terms.put("guarantee", guarantee);
        terms.put("notChanged", notChanged);
        terms.put("assignable", assignable);
        String text = start;
        int i = 0;
        for (String t: terms.keySet()) {
            String e = i < terms.size() ? br : end;
            final boolean isMod = t.equals("assignable");
            text = text + startb + t + ":" + endb
                    + (!isMod || hasMod ?
                            LogicPrinter.quickPrintTerm(terms.get(t), serv,
                                                  usePrettyPrinting,
                                                  useUnicodeSymbols)
                       : "")
                    + (isMod && !hasMod ?
                            (LogicPrinter.quickPrintTerm(serv.getTermBuilder().empty(), serv,
                                                         usePrettyPrinting,
                                                         useUnicodeSymbols)
                             + startb + ", creates no new objects" + endb) : "")
                    + e;
            i++;
        }
        return text;
    }

    @Override
    public String getHTMLText(Services serv) {
        return getText(true, serv,
                       NotationInfo.DEFAULT_PRETTY_SYNTAX,
                       NotationInfo.DEFAULT_UNICODE_ENABLED);
    }

    @Override
    public final String getPlainText(Services services) {
        return getText(false, services,
                       NotationInfo.DEFAULT_PRETTY_SYNTAX,
                       NotationInfo.DEFAULT_UNICODE_ENABLED);
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

    /**
     * Subclass for generating R/G-Taclets for assignment-read-rules as
     * elements from the thread specification are needed.
     *
     * @author Michael Kirsten
     */
    private static class TacletGenerator {

        private static SuccTaclet taclet(final String name, final String[] ruleSet,
                                         final Term find, final ImmutableList<TacletGoalTemplate> goals,
                                         final VariableCondition[] varConds,
                                         final LocationVariable threadVar,
                                         final String displayName,
                                         final Services services) {
            final TermBuilder tb = services.getTermBuilder();
            final Term exactInstance = threadVar == null ?
                    tb.ff() : tb.exactInstance(threadVar.getKeYJavaType().getSort(), tb.var(threadVar));
            final Sequent exactInstanceSeq =
                    Sequent.createAnteSequent(new Semisequent(new SequentFormula(exactInstance)));

            final SuccTacletBuilder tab = new SuccTacletBuilder();
            tab.setName(MiscTools.toValidTacletName(name));
            tab.setDisplayName(MiscTools.toValidTacletName(displayName).toString());
            for (final String s: ruleSet) {
                tab.addRuleSet(new RuleSet(new Name(s)));
            }
            tab.setFind(find);
            tab.setTacletGoalTemplates(goals);
            for (final VariableCondition varCond: varConds) {
                tab.addVariableCondition(varCond);
            }
            if (threadVar != null) {
                tab.setIfSequent(exactInstanceSeq);
            }
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
                                                   final boolean isStatic,
                                                   final Services services) {
            final TermBuilder tb = services.getTermBuilder();

            final Term heap = tb.getBaseHeap();
            final Term receiver = isStatic ? null : tb.var((ParsableVariable)fieldRef.getReferencePrefix());
            final ProgramSV pv = (ProgramSV)((SchematicFieldReference)fieldRef).getReferenceSuffix();

            final Term memberPVToField =
                    tb.tf().createTerm(AbstractTermTransformer.MEMBER_PV_TO_FIELD, tb.var(pv));
            return tb.elementary(tb.var(lhs),
                                 tb.select(g, heap, isStatic ? tb.NULL() : receiver,
                                           memberPVToField));
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
                                                            final TypeReference v,
                                                            final ThreadSpecification tspec,
                                                            final Services services) {
            final TermBuilder tb = services.getTermBuilder();
            final SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
            final boolean hasUpd = update != null;
            final Term heap = tb.getBaseHeap();
            final Term prevHeap = tb.getPrevHeap();
            final Term heaps = tb.var(seqLDT.getHeapSeq());
            final Term eStep = tb.var(seqLDT.getEStepSeq());

            final Term anonUpd = buildAnonUpd(tspec, services);
            final Term heapsUpd = tb.elementary(heaps, tb.seqConcat(heaps, tb.seqSingleton(heap)));
            final Term eStepUpd = tb.elementary(eStep, tb.seqConcat(eStep, tb.seqSingleton(tb.TRUE())));
            final Term prevUpd = tb.parallel(tb.elementary(prevHeap, heap), anonUpd);

            final Term[] upd; // update for new post condition
            if (assignUpd != null) {
                upd = hasUpd ? new Term[] {update, anonUpd, heapsUpd, eStepUpd, assignUpd} :
                    new Term[] {anonUpd, heapsUpd, eStepUpd, assignUpd};
            } else {
                upd = hasUpd ? new Term[] {update, anonUpd, heapsUpd, eStepUpd} :
                    new Term[] {anonUpd, heapsUpd, eStepUpd};
            }

            final Term rely = tspec.getRely(prevHeap, heap, tb.var(tspec.getThreadVar()), services);
            final Term addRely;
            if (rely.equalsModRenaming(tb.tt())) {
                addRely = null;
            } else { // add rely in any case
                final Term[] seqUpd = hasUpd ? new Term[] {update, prevUpd} : new Term[] {prevUpd};
                addRely = tb.applySequential(seqUpd, rely);
            }

            final Term replaceWith = tb.applySequential(upd, replaceTerm);
            final AntecSuccTacletGoalTemplate relyGoal = goal(addRely, replaceWith);
            if (v != null) {
                relyGoal.setName("Normal Execution (" + v.getName() + " != null)");
            }

            return relyGoal;
        }

        private static AntecSuccTacletGoalTemplate nullReferenceGoal(final Term prog, final Term update,
                                                                     final Operator mod,
                                                                     final ProgramSV v,
                                                                     final ExcOption exc,
                                                                     final Services services) {
            final TermBuilder tb = services.getTermBuilder();
            final Term varEqNull = update != null ?
                    tb.apply(update, tb.equals(tb.var(v), tb.NULL())) :
                        tb.equals(tb.var(v), tb.NULL());
            final Term replaceTerm;
            if (exc == ExcOption.ALLOW) {
                final New exception = KeYJavaASTFactory
                        .newOperator(services.getJavaInfo().getKeYJavaType(
                                "java.lang.NullPointerException"));
                final Throw t = KeYJavaASTFactory.throwClause(exception);
                final ContextStatementBlock throwExc =
                        new ContextStatementBlock(new Statement[] {t}, null);
                final JavaBlock throwExcJb = JavaBlock.createJavaBlock(throwExc);
                replaceTerm = tb.tf().createTerm(mod, new Term[] {prog}, null, throwExcJb);
            } else {
                replaceTerm = tb.ff();
            }
            final AntecSuccTacletGoalTemplate nullRef =
                    goal(varEqNull, update != null ? tb.apply(update, replaceTerm) : replaceTerm);
            nullRef.setName("Null Reference (" + v.getName() + " = null)");
            return nullRef;
        }

        private static AntecSuccTacletGoalTemplate indexOutOfBoundsGoal(final Term prog, final Term update,
                                                                        final Operator mod,
                                                                        final ProgramSV arr,
                                                                        final ProgramSV idx,
                                                                        final ExcOption exc,
                                                                        final Services services) {
            final TermBuilder tb = services.getTermBuilder();

            final Term index = tb.var(idx);
            final Term array = tb.var(arr);

            final Term varNeqNull = tb.not(tb.equals(array, tb.NULL()));
            final Term lengthLeqIdx = tb.leq(tb.dotLength(array), index);
            final Term idxLtZero = tb.lt(index, tb.zero());

            final Term indexOutOfBounds = update != null ?
                    tb.apply(update, tb.and(varNeqNull, tb.or(lengthLeqIdx, idxLtZero))) :
                        tb.and(varNeqNull, tb.or(lengthLeqIdx, idxLtZero));
            final Term replaceTerm;
            if (exc == ExcOption.ALLOW) {
                final New exception = KeYJavaASTFactory
                        .newOperator(services.getJavaInfo().getKeYJavaType(
                                "java.lang.ArrayIndexOutOfBoundsException"));
                Throw t = KeYJavaASTFactory.throwClause(exception);
                final ContextStatementBlock throwExc =
                        new ContextStatementBlock(new Statement[] {t}, null);
                final JavaBlock throwExcJb = JavaBlock.createJavaBlock(throwExc);
                replaceTerm = tb.tf().createTerm(mod, new Term[] {prog}, null, throwExcJb);
            } else {
                replaceTerm = tb.ff();
            }
            final AntecSuccTacletGoalTemplate outOfBounds =
                    goal(indexOutOfBounds, update != null ? tb.apply(update, replaceTerm) : replaceTerm);
            outOfBounds.setName("Index Out of Bounds (" + arr.getName() + " != null, but "
                                + idx.getName() +" Out of Bounds!)");
            return outOfBounds;
        }

        private static AntecSuccTacletGoalTemplate arrayStoreExceptionGoal(final Term prog, final Term update,
                                                                           final Operator mod,
                                                                           final ProgramSV arr,
                                                                           final ProgramSV idx,
                                                                           final ProgramSV rhs,
                                                                           final ExcOption exc,
                                                                           final Services services) {
            final TermBuilder tb = services.getTermBuilder();

            final Term index = tb.var(idx);
            final Term array = tb.var(arr);
            final Term var = tb.var(rhs);

            final Term varNeqNull = tb.not(tb.equals(array, tb.NULL()));
            final Term idxLtLength = tb.lt(index, tb.dotLength(array));
            final Term idxGeqZero = tb.geq(tb.zero(), index);
            final Term arrStorInvalid = tb.not(tb.arrayStoreValid(array, var));

            final Term arrayStoreException = update != null ?
                    tb.apply(update, tb.and(varNeqNull, idxLtLength, idxGeqZero, arrStorInvalid)) :
                        tb.and(varNeqNull, idxLtLength, idxGeqZero, arrStorInvalid);
            final Term replaceTerm;
            if (exc == ExcOption.ALLOW) {
                final New exception = KeYJavaASTFactory
                        .newOperator(services.getJavaInfo().getKeYJavaType(
                                "java.lang.ArrayStoreException"));
                final Throw t = KeYJavaASTFactory.throwClause(exception);
                final ContextStatementBlock throwExc =
                        new ContextStatementBlock(new Statement[] {t}, null);
                final JavaBlock throwExcJb = JavaBlock.createJavaBlock(throwExc);
                replaceTerm = tb.tf().createTerm(mod, new Term[] {prog}, null, throwExcJb);
            } else {
                replaceTerm = tb.ff();
            }
            final AntecSuccTacletGoalTemplate arrayStoreExc =
                    goal(arrayStoreException, update != null ? tb.apply(update, replaceTerm) : replaceTerm);
            arrayStoreExc.setName("Array Store Exception (incompatible dynamic element type of "
                                  + arr.getName() + " and " + idx.getName() +")");
            return arrayStoreExc;
        }

        private static AntecSuccTacletGoalTemplate normalFieldAccGoal(final Term prog, final Term update,
                                                                      final Operator mod,
                                                                      final ProgramSV v0,
                                                                      final SchematicFieldReference vDotA,
                                                                      final GenericSort g,
                                                                      final boolean isStatic,
                                                                      final ThreadSpecification tspec,
                                                                      final Services services) {
            final TermFactory tf = services.getTermFactory();
            final TypeReference v = (TypeReference)vDotA.getReferencePrefix();

            final Term fieldAccAssignUpd = buildFieldAccAssignUpd(v0, vDotA, g, isStatic, services);
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
            final boolean hasUpd = update != null;
            final String tName = "Rely " + name + " EmptyModality";

            final JavaBlock emptyJb = JavaBlock.createJavaBlock(new StatementBlock());
            final Term find = tb.tf().createTerm(mod, new Term[]{prog}, null, emptyJb);
            final Term findTerm = hasUpd ? tb.apply(update, find) : find;

            final AntecSuccTacletGoalTemplate goalTemp =
                    relyGoal(update, null, prog, null, tspec, services);

            return taclet(tName + (hasUpd ? "Update" : ""),
                          new String[] {"simplify_prog"},
                          findTerm, goals(goalTemp),
                          new VariableCondition[] {},
                          tspec.getThreadVar(), tName,
                          services);
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
            final boolean hasUpd = update != null;

            final ProgramSV lhs =
                    SchemaVariableFactory.createProgramSV(new ProgramElementName("#v0"),
                            ProgramSVSort.VARIABLE, false);
            final ProgramSV v =
                    SchemaVariableFactory.createProgramSV(new ProgramElementName("#v"),
                            ProgramSVSort.VARIABLE, false);
            final ProgramSV sv =
                    SchemaVariableFactory.createProgramSV(new ProgramElementName("#sv"),
                            ProgramSVSort.STATICVARIABLE, false);
            final ProgramSV a =
                    SchemaVariableFactory.createProgramSV(new ProgramElementName("#a"),
                            ProgramSVSort.VARIABLE, false);
            final GenericSort g = new GenericSort(new Name("G"));
            final SchematicFieldReference rhs = new SchematicFieldReference(a, v);
            final SchematicFieldReference rhsStatic = new SchematicFieldReference(sv, null);
            final SchematicFieldReference rhsStaticWithPrefix =
                    new SchematicFieldReference(sv, KeYJavaASTFactory.typeRef(tspec.getKJT()));// v

            final ContextStatementBlock fieldAccBlock =
                    new ContextStatementBlock(KeYJavaASTFactory.assign(lhs, rhs), null);
            final ContextStatementBlock staticFieldAccBlock =
                    new ContextStatementBlock(
                            KeYJavaASTFactory.assign(lhs,
                                    KeYJavaASTFactory.passiveExpression(rhsStatic)),
                                    null);
            final ContextStatementBlock staticFieldAccBlockWithPrefix =
                    new ContextStatementBlock(
                            KeYJavaASTFactory.assign(lhs,
                                    KeYJavaASTFactory.passiveExpression(rhsStaticWithPrefix)),
                                    null);
            final JavaBlock jb = JavaBlock.createJavaBlock(fieldAccBlock);
            final JavaBlock jbStatic = JavaBlock.createJavaBlock(staticFieldAccBlock);
            final JavaBlock jbStaticWithPrefix = JavaBlock.createJavaBlock(staticFieldAccBlockWithPrefix);
            final Term findTerm = hasUpd ?
                    tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jb)) :
                        tf.createTerm(mod, new Term[]{prog}, null, jb);
            final Term findTermStatic = hasUpd ?
                    tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbStatic)) :
                        tf.createTerm(mod, new Term[]{prog}, null, jbStatic);
            final Term findTermStaticWithPrefix = hasUpd ?
                    tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbStaticWithPrefix)) :
                        tf.createTerm(mod, new Term[]{prog}, null, jbStaticWithPrefix);

            final AntecSuccTacletGoalTemplate normalExec =
                    normalFieldAccGoal(prog, update, mod, lhs, rhs, g, false, tspec, services);
            final AntecSuccTacletGoalTemplate normalStaticExec =
                    normalFieldAccGoal(prog, update, mod, lhs, rhsStatic, g, true, tspec, services);
            final AntecSuccTacletGoalTemplate normalStaticExecWithPrefix =
                    normalFieldAccGoal(prog, update, mod, lhs, rhsStaticWithPrefix, g, true, tspec, services);
            final AntecSuccTacletGoalTemplate nullRef =
                    nullReferenceGoal(prog, update, mod, v, exc, services);

            final ImmutableList<TacletGoalTemplate> fieldAccGoals;
            final ImmutableList<TacletGoalTemplate> staticFieldAccGoals = goals(normalStaticExec);
            final ImmutableList<TacletGoalTemplate> staticFieldAccWithPrefixGoals =
                    goals(normalStaticExecWithPrefix);
            final ImmutableList<TacletGoalTemplate> fieldAccThisGoals;
            String tName = null;
            switch (exc) {
                case IGNORE:
                    fieldAccGoals = goals(normalExec);
                    fieldAccThisGoals = goals(normalExec);
                    break;
                case BAN: case ALLOW:
                    fieldAccGoals = goals(normalExec, nullRef);
                    fieldAccThisGoals = goals(normalExec);
                    break;
                default:
                    throw new RuntimeException("The setting for the RuntimeException-option is not valid: "
                                               + exc);
            }

            tName = "Rely " + name + " assignmentReadStaticAttribute";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog", "simplify_prog_subset"},
                                 findTermStatic, staticFieldAccGoals,
                                 new VariableCondition[] { new FinalReferenceCondition(sv, true),
                                                           new StaticReferenceCondition(sv, false),
                                                           new JavaTypeToSortCondition(sv, g, false)},
                                 tspec.getThreadVar(), tName, services));
            tName = "Rely " + name + " assignmentReadStaticAttributeWithVariablePrefix";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog"},
                                 findTermStaticWithPrefix, staticFieldAccWithPrefixGoals,
                                 new VariableCondition[] { new FinalReferenceCondition(sv, true),
                                                           new StaticReferenceCondition(sv, false),
                                                           new JavaTypeToSortCondition(sv, g, false)},
                                 null, tName, services));
            tName = "Rely " + name + " assignmentReadAttribute";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog", "simplify_prog_subset"},
                                 findTerm, fieldAccGoals,
                                 new VariableCondition[] { new FinalReferenceCondition(a, true),
                                                           new ArrayLengthCondition(a, true),
                                                           new StaticReferenceCondition(a, true),
                                                           new IsThisReference(v, true),
                                                           new JavaTypeToSortCondition(a, g, false)},
                                 tspec.getThreadVar(), tName, services));
            tName = "Rely " + name + " assignmentReadAttributeThis";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog", "simplify_prog_subset"},
                                 findTerm, fieldAccThisGoals,
                                 new VariableCondition[] { new FinalReferenceCondition(a, true),
                                                           new ArrayLengthCondition(a, true),
                                                           new StaticReferenceCondition(a, true),
                                                           new IsThisReference(v, false),
                                                           new JavaTypeToSortCondition(a, g, false)},
                                 tspec.getThreadVar(), tName, services));
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
            final boolean hasUpd = update != null;

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
            final Term findTermToArr = update != null ?
                    tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbToArr)) :
                        tf.createTerm(mod, new Term[]{prog}, null, jbToArr);

            final ContextStatementBlock arrToAssignBlock =
                    new ContextStatementBlock(KeYJavaASTFactory.assign(expr, arrRef), null);
            final JavaBlock jbArrTo = JavaBlock.createJavaBlock(arrToAssignBlock);
            final Term findTermArrTo = update != null ?
                    tb.apply(update, tf.createTerm(mod, new Term[]{prog}, null, jbArrTo)) :
                        tf.createTerm(mod, new Term[]{prog}, null, jbArrTo);

            final AntecSuccTacletGoalTemplate normalToArrExec =
                    normalToArrayRefGoal(prog, update, mod, arrRef, expr, tspec, services);
            final AntecSuccTacletGoalTemplate normalArrAccExec =
                    normalArrayAccGoal(prog, update, mod, arrRef, expr, g, tspec, services);

            final AntecSuccTacletGoalTemplate nullRef =
                    nullReferenceGoal(prog, update, mod, v, exc, services);
            final AntecSuccTacletGoalTemplate indexOutOfBounds =
                    indexOutOfBoundsGoal(prog, update, mod, v, se, exc, services);
            final AntecSuccTacletGoalTemplate arrayStoreException =
                    arrayStoreExceptionGoal(prog, update, mod, v, se, expr, exc, services);

            final ImmutableList<TacletGoalTemplate> assignToRefArrGoals;
            final ImmutableList<TacletGoalTemplate> assignToPrimArrGoals;
            final ImmutableList<TacletGoalTemplate> arrAccGoals;
            String tName = null;
            switch (exc) {
                case IGNORE:
                    assignToRefArrGoals = goals(normalToArrExec);
                    assignToPrimArrGoals = goals(normalToArrExec);
                    arrAccGoals = goals(normalArrAccExec);
                    break;
                case BAN: case ALLOW:
                    assignToRefArrGoals = goals(normalToArrExec, nullRef, indexOutOfBounds, arrayStoreException);
                    assignToPrimArrGoals = goals(normalToArrExec, nullRef, indexOutOfBounds);
                    arrAccGoals = goals(normalArrAccExec, nullRef, indexOutOfBounds);
                    break;
                default:
                    throw new RuntimeException("The setting for the RuntimeException-option is not valid: "
                            + exc);
            }

            tName = "Rely " + name + " assignmentToReferenceArrayComponent";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog", "simplify_prog_subset"},
                                 findTermToArr, assignToRefArrGoals,
                                 new VariableCondition[] { new ArrayComponentTypeCondition(v, true) },
                                 tspec.getThreadVar(), tName, services));
            tName = "Rely " + name + " assignmentToPrimitiveArrayComponent";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog", "simplify_prog_subset"},
                                 findTermToArr, assignToPrimArrGoals,
                                 new VariableCondition[] { new ArrayComponentTypeCondition(v, false) },
                                 tspec.getThreadVar(), tName, services));
            tName = "Rely " + name + " assignmentArray2";
            res = res.add(taclet(tName + (hasUpd ? "Update" : ""),
                                 new String[] {"simplify_prog", "simplify_prog_subset"},
                                 findTermArrTo, arrAccGoals,
                                 new VariableCondition[] { new JavaTypeToSortCondition(v, g, true) },
                                 tspec.getThreadVar(), tName, services));
            return res;
        }

        private static ImmutableSet<SuccTaclet> createTaclets(final String name, final Term post,
                                                              final Term update, final ModalOperatorSV mod,
                                                              final ThreadSpecification tspec,
                                                              final ExcOption exc, final Services services) {
            ImmutableSet<SuccTaclet> taclets;
            taclets = createFieldAccTaclets(name, post, update, mod, tspec, exc, services);
            taclets = taclets.union(createArrayAccTaclets(name, post, update, mod, tspec, exc, services));
            taclets = taclets.add(createEmptyModTaclet(name, post, update, mod, tspec, services));
            return taclets;
        }
    }
}