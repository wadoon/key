package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.JMLResolverManager;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator;
import de.uka.ilkd.key.speclang.translation.*;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
public class ExpressionTranslator extends JmlParserBaseVisitor<Object> {
    /**
     * maximum valid value of a signed int
     */
    private static final BigInteger MAX_INT = BigInteger.valueOf(Integer.MAX_VALUE);

    /**
     * maximum valid value of a signed long
     */
    private static final BigInteger MAX_LONG = BigInteger.valueOf(Long.MAX_VALUE);

    /**
     * maximum valid value if an int was interpreted unsigned
     */
    private static final BigInteger MAX_UINT = new BigInteger("4294967295");

    /**
     * maximum valid value if a long was interpreted unsigned
     */
    private static final BigInteger MAX_ULONG = new BigInteger("18446744073709551615");

    private final TermBuilder tb;
    private final Services services;
    private final JavaInfo javaInfo;
    private final KeYJavaType containerType;
    private final IntegerLDT intLDT;
    private final HeapLDT heapLDT;
    private final LocSetLDT locSetLDT;
    private final BooleanLDT booleanLDT;
    private final SLTranslationExceptionManager excManager;
    private final List<PositionedString> warnings = new java.util.ArrayList<PositionedString>();

    private final JMLTranslator translator;

    private final ProgramVariable selfVar;
    private final ImmutableList<ProgramVariable> paramVars;
    private final ProgramVariable resultVar;
    private final ProgramVariable excVar;
    private final Map<LocationVariable, Term> atPres;
    private final Map<LocationVariable, Term> atBefores;

    // Helper objects
    private final JMLResolverManager resolverManager;
    private final JavaIntegerSemanticsHelper intHelper;

    private ExpressionTranslator(Services services,
                                 KeYJavaType specInClass,
                                 ProgramVariable self,
                                 ImmutableList<ProgramVariable> paramVars,
                                 ProgramVariable result,
                                 ProgramVariable exc,
                                 Map<LocationVariable, Term> atPres,
                                 Map<LocationVariable, Term> atBefores) {
        // save parameters
        this.services = services;
        this.tb = services.getTermBuilder();
        this.javaInfo = services.getJavaInfo();
        containerType = specInClass;
        this.intLDT = services.getTypeConverter().getIntegerLDT();
        this.heapLDT = services.getTypeConverter().getHeapLDT();
        this.locSetLDT = services.getTypeConverter().getLocSetLDT();
        this.booleanLDT = services.getTypeConverter().getBooleanLDT();
        this.excManager =
                new SLTranslationExceptionManager(null, "",
                        new Position(0, 0));
        this.translator = new JMLTranslator(excManager, "",
                services);

        this.selfVar = self;
        this.paramVars = paramVars;
        this.resultVar = result;
        this.excVar = exc;
        this.atPres = atPres;
        this.atBefores = atBefores;

        intHelper = new JavaIntegerSemanticsHelper(services, excManager);
        // initialize helper objects
        this.resolverManager = new JMLResolverManager(this.javaInfo,
                specInClass,
                selfVar,
                this.excManager);

        // initialize namespaces
        resolverManager.pushLocalVariablesNamespace();
        if (paramVars != null) {
            resolverManager.putIntoTopLocalVariablesNamespace(paramVars);
        }
        if (resultVar != null) {
            resolverManager.putIntoTopLocalVariablesNamespace(resultVar);
        }
    }

    public SLTranslationExceptionManager getExceptionManager() {
        return excManager;
    }


    private void raiseError(String s, Token symbol) {
        raiseError(s);
    }

    private void raiseError(String msg) {
        throw new RuntimeException(excManager.createException(msg));
    }

    /*private void raiseError(String msg, Token t)
            throws SLTranslationException {
        throw excManager.createException(msg, t);
    }

    private void raiseNotSupported(String feature)
            throws SLTranslationException {
        throw excManager.createWarningException(feature + " not supported");
    }*/

    /**
     * This is used for features without semantics such as
     * labels or annotations.
     *
     * @author bruns
     * @since 1.7.2178
     */
    private void addIgnoreWarning(String feature, Token t) {
        String msg = feature + " is not supported and has been silently ignored.";
        warnings.add(new PositionedString(msg, t.getTokenSource().getSourceName(),
                new Position(t.getLine(), t.getCharPositionInLine())));
    }

    public List<PositionedString> getWarnings() {
        List<PositionedString> res =
                new ArrayList<PositionedString>(warnings.size());
        res.addAll(translator.getWarnings());
        return res;
    }

    /**
     * Extracts a term's subterms as an array.
     */
    private Term[] getSubTerms(Term term) {
        Term[] result = new Term[term.arity()];
        for (int i = 0; i < term.arity(); i++) {
            result[i] = term.sub(i);
            assert result[i] != null;
        }
        return result;
    }

    /**
     * Extracts the sorts from an array of terms as an array.
     */
    private Sort[] getSorts(Term[] terms) {
        Sort[] result = new Sort[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] = terms[i].sort();
        }
        return result;
    }

    private LocationVariable getBaseHeap() {
        return services.getTypeConverter().getHeapLDT().getHeap();
    }

    private LocationVariable getSavedHeap() {
        return services.getTypeConverter().getHeapLDT().getSavedHeap();
    }

    private LocationVariable getPermissionHeap() {
        return services.getTypeConverter().getHeapLDT().getPermissionHeap();
    }

    /**
     * Converts a term so that all of its non-rigid operators refer to the
     * pre-state of the current method.
     */
    // TODO: remove when all clients have been moved to JMLTranslator
    private Term convertToOld(final Term term) {
        assert atPres != null && atPres.get(getBaseHeap()) != null;
        Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        for (LocationVariable var : atPres.keySet()) {
            // caution: That may now also be other variables than only heaps.
            Term varAtPre = atPres.get(var);
            if (varAtPre != null) {
                map.put(tb.var(var), varAtPre);
            }
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }

    /**
     * Converts a term so that all of its non-rigid operators refer to the
     * pre-state of the current block ().
     */
    // TODO: remove when all clients have been moved to JMLTranslator
    private Term convertToBefore(final Term term) {
        assert atBefores != null && atBefores.get(getBaseHeap()) != null;
        Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        for (LocationVariable var : atBefores.keySet()) {
            // caution: That may now also be other variables than only heaps.
            Term varAtPre = atBefores.get(var);
            if (varAtPre != null) {
                map.put(tb.var(var), varAtPre);
            }
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }

    private Term convertToBackup(Term term) {
        assert atPres != null && atPres.get(getSavedHeap()) != null;
        Map map = new LinkedHashMap();
        map.put(tb.var(getBaseHeap()), tb.var(getSavedHeap()));
        if (atPres.get(getBaseHeap()) != null) {
            map.put(atPres.get(getBaseHeap()), atPres.get(getSavedHeap()));
        }
        OpReplacer or = new OpReplacer(map, tb.tf());
        return or.replace(term);
    }

    private Term convertToPermission(Term term) {
        LocationVariable permissionHeap = getPermissionHeap();
        if (permissionHeap == null) {
            raiseError("\\permission expression used in a non-permission" +
                    " context and permissions not enabled.");
        }
        if (!term.op().name().toString().endsWith("::select")) {
            raiseError("\\permission expression used with non store-ref" +
                    " expression.");
        }
        return tb.select(
                services.getTypeConverter().getPermissionLDT().targetSort(),
                tb.var(getPermissionHeap()), term.sub(1), term.sub(2));
    }

    private String createSignatureString(ImmutableList<SLExpression> signature) {
        if (signature == null || signature.isEmpty()) {
            return "";
        }
        String sigString = "";

        for (SLExpression expr : signature) {
            final KeYJavaType t = expr.getType();
            sigString += (t == null ? "<unknown type>" : t.getFullName()) + ", ";
        }

        return sigString.substring(0, sigString.length() - 2);
    }

    @Override
    public Term visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
        return translator.get(ctx.ACCESSIBLE().getText(), accept(ctx.storeRefUnion()), services);
    }

    @Override
    public Term visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        if (ctx.STRICTLY_NOTHING() != null) return tb.strictlyNothing();
        else return translator.get(ctx.ASSIGNABLE().getText(), accept(ctx.storeRefUnion()), services);
    }

    private <T> @Nullable T accept(@Nullable ParserRuleContext ctx) {
        return (T) ctx.accept(this);
    }


    @Override
    public Triple<ObserverFunction, Term, Term> visitDepends_clause(JmlParser.Depends_clauseContext ctx) {
        Term lhs = accept(ctx.expression(0));
        Term rhs = accept(ctx.storeRefUnion());
        Term mby = accept(ctx.expression(1));
        return translator.get(ctx.DEPENDS().getText(), lhs, rhs, mby, services);
    }

    /*decreasesclause returns[
    Term ret = null]throws SLTranslationException

    @after {
        ret = result;
    }
:
    dec=
    DECREASES result = termexpression
            (COMMA t = termexpression

    {
        result = tb.pair(result, t);
    } )*;
*/


    @Override
    public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        return translator.get(ctx.REQUIRES().getText(), accept(ctx.predornot()), services);
    }

    @Override
    public Object visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
        return translator.get(ctx.ENSURES().getText(), accept(ctx.predornot()), services);
    }


    @Override
    public Term visitAxioms_clause(JmlParser.Axioms_clauseContext ctx) {
        return translator.get(ctx.MODEL_METHOD_AXIOM().getText(),
                accept(ctx.termexpression()), services);
    }

    @Override
    public Pair<ObserverFunction, Term> visitRepresents_clause(JmlParser.Represents_clauseContext ctx) {
        //TODO
        SLExpression lhs = accept(ctx.lhs);
        boolean representsClauseLhsIsLocSet = lhs.getTerm().sort().equals(locSetLDT.targetSort());
        if (!lhs.isTerm()
                || !(lhs.getTerm().op() instanceof ObserverFunction)
                || lhs.getTerm().sub(0).op() != heapLDT.getHeap()) {
            raiseError("Represents clause with unexpected lhs: " + lhs);
        } else if (selfVar != null
                && ((ObserverFunction) lhs.getTerm().op()).isStatic()) {
            raiseError("Represents clauses for static model fields must be static.");
        }

        Term t;
        if (representsClauseLhsIsLocSet) {
            SLExpression rhs = accept(ctx.rhs);
            if (!rhs.isTerm()) {
                raiseError("Represents clause with unexpected rhs: " + rhs);
            }
            Term rhsTerm = rhs.getTerm();
            if (rhsTerm.sort() == Sort.FORMULA) {
                rhsTerm = tb.ife(rhsTerm, tb.TRUE(), tb.FALSE());
            }
            t = tb.equals(lhs.getTerm(), rhsTerm);
        } else {
            t = accept(ctx.storeRefUnion());
            t = tb.equals(lhs.getTerm(), t);
        }
        if (ctx.SUCH_THAT() != null) t = accept(ctx.predicate());
        return translator.get(ctx.REPRESENTS().getText(), lhs, t, services);
    }

    public KeYJavaType visitBuiltintype(JmlParser.BuiltintypeContext ctx) {
        if (ctx.BYTE() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_BYTE);
        if (ctx.SHORT() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_SHORT);
        if (ctx.INT() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT);
        if (ctx.LONG() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG);
        if (ctx.BOOLEAN() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
        if (ctx.VOID() != null) return KeYJavaType.VOID_TYPE;
        if (ctx.BIGINT() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_BIGINT);
        if (ctx.REAL() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_REAL);
        if (ctx.LOCSET() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_LOCSET);
        if (ctx.SEQ() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_SEQ);
        if (ctx.FREE() != null) return javaInfo.getKeYJavaType(PrimitiveType.JAVA_FREE_ADT);
        return null;
    }

    @Override
    public InfFlowSpec visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
        ImmutableList<Term> decl = ImmutableSLList.nil();
        ImmutableList<Term> erases = ImmutableSLList.nil();
        ImmutableList<Term> newObs = ImmutableSLList.nil();

        ImmutableList<Term> sep = accept(ctx.sep);

        decl = decl.append((Iterable<Term>) accept(ctx.decl));
        erases = erases.append((Iterable<Term>) accept(ctx.decl));
        newObs = newObs.append((Iterable<Term>) accept(ctx.newobj));
        decl = sep.append(decl);
        erases = sep.append(erases);
        return new InfFlowSpec(decl, erases, newObs);
        //return InfFlowSpec.EMPTY_INF_FLOW_SPEC;
    }

    @Override
    public Object visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
        InfFlowSpec result = InfFlowSpec.EMPTY_INF_FLOW_SPEC;
        ImmutableList<Term> sep = sep = accept(ctx.sep);
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        newObs = newObs.append((Iterable<Term>) accept(ctx.newobj));
        return new InfFlowSpec(sep, sep, newObs);
    }

    @Override
    public Object visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
        ImmutableList<Term> decl = ImmutableSLList.nil();
        ImmutableList<Term> erases = ImmutableSLList.nil();
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        ImmutableList<Term> det = accept(ctx.det);
        ImmutableList<Term> by = ImmutableSLList.nil();

        if (ctx.ITSELF() != null) by = det;
        else by = append(by, ctx.by);


        decl = append(decl, ctx.decl);
        erases = append(erases, ctx.erases);
        newObs = append(newObs, ctx.newObs);

        det = det.append(erases);
        by = by.append(decl);
        return new InfFlowSpec(by, det, newObs);
    }

    private <T> ImmutableList<T> append(ImmutableList<T> by,
                                        ParserRuleContext ctx) {
        return by.append((T) accept(ctx));
    }

    private <T> ImmutableList<T> append(ImmutableList<T> target,
                                        List<? extends ParserRuleContext> ctx) {
        for (ParserRuleContext c : ctx) {
            target = target.append((T) accept(c));
        }
        return target;
    }

    @Override
    public Object visitLoop_determines_clause(JmlParser.Loop_determines_clauseContext ctx) {
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        ImmutableList<Term> det = append(ImmutableSLList.nil(), ctx.det);
        //TODO BY ITSELF?
        newObs = append(newObs, ctx.newObs);
        return new InfFlowSpec(det, det, newObs);
    }

    @Override
    public ImmutableList<Term> visitInfflowspeclist(JmlParser.InfflowspeclistContext ctx) {
        ImmutableList<Term> result = listOf(ctx.termexpression());
        return translator.get("infflowspeclist", result, services);
    }

    @Override
    public Object visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
        LogicVariable eVar = null;
        KeYJavaType excType = accept(ctx.referencetype());
        String vName = accept(ctx.IDENT());
        Term pred = null;
        if (vName != null) {
            eVar = new LogicVariable(new Name(vName), excType.getSort());
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(eVar, excType);
        }
        Term result = accept(ctx.predornot());
        if (vName != null) {
            resolverManager.popLocalVariablesNamespace();
        }
        return translator.get(ctx.SIGNALS().getText(), result, eVar, excVar, excType, services);
    }

    private @Nullable String accept(@Nullable TerminalNode ident) {
        if (ident == null) return null;
        return ident.getText();
    }


    @Override
    public Object visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        ImmutableList<KeYJavaType> typeList = ImmutableSLList.nil();
        for (JmlParser.ReferencetypeContext context : ctx.referencetype()) {
            typeList = typeList.append((KeYJavaType) accept(context));
        }
        return translator.get(ctx.SIGNALS_ONLY().getText(), typeList, this.excVar, services);
    }

    /*TODO
    mergeparamsspec returns[
    MergeParamsSpec result = null]throws SLTranslationException

    @init {
        ImmutableList<Term> preds = ImmutableSLList.<Term>nil();
        LocationVariable placeholder = null;
    }
:

    MERGE_PARAMS

    LBRACE

            (latticetype =IDENT)

    COLON

    LPAREN
            (phType =typespec)
            (phName =IDENT)

    {
        placeholder = new LocationVariable(new ProgramElementName(phName.getText()), phType);
        resolverManager.putIntoTopLocalVariablesNamespace(placeholder);
    }

    RPAREN

            RARROW

    LBRACE
            (abstrPred =predicate) {
        preds = preds.prepend(abstrPred);
    }
            (

    COMMA
            (abstrPred =predicate) {
        preds = preds.prepend(abstrPred);
    }
            )*
    RBRACE

            RBRACE

    {
        result = new MergeParamsSpec(latticetype.getText(), placeholder, preds);
    }

    ;
     */

    @Override
    public Object visitTermexpression(JmlParser.TermexpressionContext ctx) {
        return ((SLExpression) accept(ctx.expression())).getTerm();
    }

    @Override
    public Pair visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        String label = ctx.IDENT().getText();
        Object pred = accept(ctx.predornot());
        return translator.get(ctx.BREAKS().getText(), pred, label, services);
    }

    @Override
    public Pair visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        String label = ctx.IDENT().getText();
        Object pred = accept(ctx.predornot());
        return translator.get(ctx.CONTINUES().getText(), pred, label, services);
    }

    @Override
    public Pair visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        Object pred = accept(ctx.predornot());
        return translator.get(ctx.RETURNS().getText(), pred, services);
    }

    @Override
    public Object visitStoreRefUnion(JmlParser.StoreRefUnionContext ctx) {
        return tb.union((Iterable<Term>) accept(ctx.storeRefList()));
    }


    @Override
    public Object visitStoreRefList(JmlParser.StoreRefListContext ctx) {
        ImmutableList<Term> result = ImmutableSLList.nil();
        for (JmlParser.StorerefContext context : ctx.storeref()) {
            result = result.append((Term) accept(context));
        }
        return result;
    }

    @Override
    public Object visitStoreRefIntersect(JmlParser.StoreRefIntersectContext ctx) {
        return tb.intersect((Iterable<Term>) accept(ctx.storeRefList()));
    }

    @Override
    public Object visitStoreref(JmlParser.StorerefContext ctx) {
        if (null != ctx.NOTHING()) return tb.empty();
        if (null != ctx.EVERYTHING()) return tb.createdLocs();
        if (null != ctx.NOT_SPECIFIED()) return tb.createdLocs();
        else
            return accept(ctx.storeRefExpr());
    }

    @Override
    public Object visitCreateLocset(JmlParser.CreateLocsetContext ctx) {
        //TODO? (LOCSET | SINGLETON)
        return translator.get("create locset", accept(ctx.exprList()), services);
    }


    @Override
    public ImmutableList<SLExpression> visitExprList(JmlParser.ExprListContext ctx) {
        ImmutableList<SLExpression> result = ImmutableSLList.nil();
        for (JmlParser.ExpressionContext context : ctx.expression()) {
            result = result.append((SLExpression) accept(context));
        }
        return result;
    }

    @Override
    public Object visitStoreRefExpr(JmlParser.StoreRefExprContext ctx) {
        return translator.get("store_ref_expr", accept(ctx.expression()), services);
    }


    @Override
    public Term visitPredornot(JmlParser.PredornotContext ctx) {
        if (ctx.predicate() != null) return accept(ctx.predicate());
        if (ctx.NOT_SPECIFIED() != null)
            return translator.createSkolemExprBool(ctx.NOT_SPECIFIED().getText()).getTerm();
        if (ctx.SAME() != null) {
            return null; //TODO check
        }
        return null;
    }

    @Override
    public Object visitPredicate(JmlParser.PredicateContext ctx) {
        SLExpression expr = accept(ctx.expression());
        if (!expr.isTerm() && expr.getTerm().sort() == Sort.FORMULA) {
            raiseError("Expected a formula: " + expr);
        }
        return expr.getTerm();
    }

    @Override
    public SLExpression visitExpression(JmlParser.ExpressionContext ctx) {
        SLExpression result = accept(ctx.conditionalexpr());
        if (!result.isTerm()) {
            raiseError("Expected a term: " + result);
        }
        return result;
    }

    @Override
    public SLExpression visitConditionalexpr(JmlParser.ConditionalexprContext ctx) {
        SLExpression cond = accept(ctx.equivalenceexpr());
        SLExpression then = accept(ctx.conditionalexpr(0));
        SLExpression else_ = accept(ctx.conditionalexpr(1));
        return translator.get(JMLTranslator.JMLKeyWord.CONDITIONAL.jmlName(), services, cond, then, else_);
    }

    @Override
    public Object visitEquivalenceexpr(JmlParser.EquivalenceexprContext ctx) {
        SLExpression left = accept(ctx.impliesexpr(0));
        SLExpression right = accept(ctx.impliesexpr(1));
        return translator.get(ctx.EQV_ANTIV(0).getText(), left, right, services);
    }

    /*
     * Note: According to JML Manual 12.6.3 forward implication has to be parsed right-associatively
     * and backward implication left-associatively.
     */
    @Override
    public Object visitImpliesexpr(JmlParser.ImpliesexprContext ctx) {
        SLExpression ret = null;
        SLExpression result = accept(ctx.a);
        if (ctx.IMPLIES() != null) {
            SLExpression expr = accept(ctx.b);
            result = new SLExpression(tb.imp(tb.convertToFormula(result.getTerm()),
                    tb.convertToFormula(expr.getTerm())));
        }
        if (!ctx.IMPLIESBACKWARD().isEmpty()) {
            List<SLExpression> exprs = mapOf(ctx.c);
            for (SLExpression expr : exprs) {
                result = new SLExpression(tb.imp(tb.convertToFormula(expr.getTerm()),
                        tb.convertToFormula(result.getTerm())));
            }
        }
        return result;
    }

    @Override
    public SLExpression visitImpliesforwardexpr(JmlParser.ImpliesforwardexprContext ctx) {
        SLExpression result = accept(ctx.a);
        if (ctx.b != null) {
            SLExpression expr = accept(ctx.b);
            return new SLExpression(tb.imp(tb.convertToFormula(result.getTerm()),
                    tb.convertToFormula(expr.getTerm())));
        }
        return result;
    }

    @Override
    public SLExpression visitLogicalorexpr(JmlParser.LogicalorexprContext ctx) {
        List<SLExpression> seq = mapOf(ctx.logicalandexpr());
        return seq.stream().reduce((a, b) ->
                new SLExpression(tb.orSC(tb.convertToFormula(a.getTerm()),
                        tb.convertToFormula(b.getTerm())))).orElse(null);
    }

    private <T> List<T> mapOf(List<? extends ParserRuleContext> contexts) {
        return contexts.stream().map(it -> (T) accept(it)).collect(Collectors.toList());
    }

    private <T> ImmutableList<T> listOf(List<? extends ParserRuleContext> contexts) {
        ImmutableList<T> seq = ImmutableSLList.nil();
        for (ParserRuleContext context : contexts) {
            seq = seq.append((T) accept(context));
        }
        return seq;
    }


    @Override
    public Object visitLogicalandexpr(JmlParser.LogicalandexprContext ctx) {
        List<SLExpression> seq = mapOf(ctx.inclusiveorexpr());
        return seq.stream().reduce((a, b) ->
                new SLExpression(tb.andSC(tb.convertToFormula(a.getTerm()),
                        tb.convertToFormula(b.getTerm())))).orElse(null);
    }

    @Override
    public Object visitInclusiveorexpr(JmlParser.InclusiveorexprContext ctx) {
        List<SLExpression> seq = mapOf(ctx.exclusiveorexpr());
        SLExpression result = seq.get(0);
        for (int i = 1; i < seq.size(); i++) {
            SLExpression expr = seq.get(i);
            if (intHelper.isIntegerTerm(result)) {
                try {
                    result = intHelper.buildPromotedOrExpression(result, expr);
                } catch (SLTranslationException e) {
                    throw new RuntimeException(e);
                }
            } else {
                result = new SLExpression(
                        tb.or(tb.convertToFormula(result.getTerm()),
                                tb.convertToFormula(expr.getTerm())));
            }
        }
        return result;
    }

    @Override
    public Object visitExclusiveorexpr(JmlParser.ExclusiveorexprContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.andexpr());
        SLExpression result = exprs.get(0);
        for (int i = 0; i < exprs.size(); i++) {
            SLExpression expr = exprs.get(i);
            if (intHelper.isIntegerTerm(result)) {
                try {
                    result = intHelper.buildPromotedXorExpression(result, expr);
                } catch (SLTranslationException e) {
                    throw new RuntimeException(e);
                }
            } else {
                Term resultFormula = tb.convertToFormula(result.getTerm());
                Term exprFormula = tb.convertToFormula(expr.getTerm());
                result = new SLExpression(tb.or(tb.and(resultFormula, tb.not(exprFormula)),
                        tb.and(tb.not(resultFormula), exprFormula)));
            }
        }
        return result;
    }

    @Override
    public Object visitAndexpr(JmlParser.AndexprContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.equalityexpr());
        SLExpression result = exprs.get(0);
        for (int i = 0; i < exprs.size(); i++) {
            SLExpression expr = exprs.get(i);
            if (intHelper.isIntegerTerm(result)) {
                try {
                    result = intHelper.buildPromotedAndExpression(result, expr);
                } catch (SLTranslationException e) {
                    throw new RuntimeException(e);
                }
            } else {
                result = new SLExpression(tb.and(tb.convertToFormula(result.getTerm()),
                        tb.convertToFormula(expr.getTerm())));
            }
        }
        return result;
    }

    @Override
    public SLExpression visitEqualityexpr(JmlParser.EqualityexprContext ctx) {
        List<SLExpression> expr = mapOf(ctx.relationalexpr());
        SLExpression result = expr.get(0);
        for (int i = 1; i < expr.size(); i++) {
            TerminalNode tok = ctx.EQ_NEQ(i);
            result = translator.get(tok.getText(), result, expr.get(i), services);
        }
        return result;
    }

    @Override
    public SLExpression visitInstance_of(JmlParser.Instance_ofContext ctx) {
        SLExpression result = accept(ctx.shiftexpr());
        KeYJavaType rtype = accept(ctx.typespec());
        SortDependingFunction f = rtype.getSort().getInstanceofSymbol(services);
        // instanceof-expression
        return new SLExpression(
                tb.and(tb.not(tb.equals(result.getTerm(), tb.NULL())),
                        tb.equals(tb.func(f, result.getTerm()), tb.TRUE())));
    }

    @Override
    public Object visitSt_expr(JmlParser.St_exprContext ctx) {
        SLExpression result = accept(ctx.shiftexpr(0));
        SLExpression right = accept(ctx.shiftexpr(1));
        if (result.isTerm() || right.isTerm()) {
            raiseError("Cannot build subtype expression from terms.", ctx.ST().getSymbol());
        }
        assert result.isType();
        assert right.isType();
        if (result.getTerm() == null) {
            addIgnoreWarning("subtype expression <: only supported for" +
                    " \\typeof() arguments on the left side.", ctx.ST().getSymbol());
            final Namespace<Function> fns = services.getNamespaces().functions();
            int x = -1;
            Name name = null;
            do name = new Name("subtype_" + ++x);
            while (fns.lookup(name) != null);
            final Function z = new Function(name, Sort.FORMULA);
            fns.add(z);
            result = new SLExpression(tb.func(z));
        } else {
            Sort os = right.getType().getSort();
            Function ioFunc = os.getInstanceofSymbol(services);
            result = new SLExpression(
                    tb.equals(
                            tb.func(ioFunc, result.getTerm()),
                            tb.TRUE()));
        }
        return result;
    }


    @Override
    public Object visitRelational_lockset(JmlParser.Relational_locksetContext ctx) {
        Function f = null;
        SLExpression left = accept(ctx.shiftexpr());
        SLExpression right = accept(ctx.postfixexpr());

        if (ctx.LOCKSET_LEQ() != null) {
            addIgnoreWarning("Lockset ordering is not supported", ctx.LOCKSET_LEQ().getSymbol());
            final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
            f = new Function(new Name("lockset_leq"), Sort.FORMULA, objSort, objSort);
        }
        if (ctx.LOCKSET_LT() != null) {
            addIgnoreWarning("Lockset ordering is not supported", ctx.LOCKSET_LT().getSymbol());
            final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
            f = new Function(new Name("lockset_lt"), Sort.FORMULA, objSort, objSort);
        }
        assert f != null;
        return new SLExpression(tb.func(f, left.getTerm(), right.getTerm()));
    }

    @Override
    public SLExpression visitRelational_chain(JmlParser.Relational_chainContext ctx) {
        List<SLExpression> expressions = mapOf(ctx.shiftexpr());
        SLExpression result = null;
        for (int i = 1; i < expressions.size() - 1; i++) {
            Function f = null;
            Token op = ctx.op.get(i);
            switch (op.getType()) {
                case JmlLexer.LT:
                    f = intLDT.getLessThan();
                    break;
                case JmlLexer.GT:
                    f = intLDT.getGreaterThan();
                    break;

                case JmlLexer.GEQ:
                    f = intLDT.getGreaterOrEquals();
                    break;
                case JmlLexer.LEQ:
                    f = intLDT.getLessOrEquals();
                    break;

            }

            SLExpression left = expressions.get(i);
            SLExpression right = expressions.get(i + 1);
            SLExpression rel = new SLExpression(tb.func(f, left.getTerm(), right.getTerm()));
            if (result == null) {
                result = rel;
            } else {
                result = new SLExpression(tb.and(result.getTerm(), rel.getTerm()));
            }
        }
        return result;
    }


    @Override
    public Object visitShiftexpr(JmlParser.ShiftexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.additiveexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String op = ctx.op.get(i).getText();
            result = translator.get(op, services, result, e);
        }
        return result;
    }

    @Override
    public Object visitAdditiveexpr(JmlParser.AdditiveexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.multexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String op = ctx.op.get(i).getText();
            result = translator.get(op, services, result, e);
        }
        return result;
    }

    @Override
    public Object visitMultexpr(JmlParser.MultexprContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.unaryexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
            Token op = ctx.op.get(i);
            SLExpression e = exprs.get(i);
            if (result.isType()) {
                raiseError("Cannot build multiplicative expression from type " +
                        result.getType().getName() + ".");
            }
            if (e.isType()) {
                raiseError("Cannot multiply by type " +
                        e.getType().getName() + ".");
            }
            try {
                switch (op.getType()) {
                    case JmlLexer.MULT:
                        result = intHelper.buildMulExpression(result, e);
                        break;
                    case JmlLexer.DIV:
                        result = intHelper.buildDivExpression(result, e);
                        break;
                    case JmlLexer.MOD:
                        result = intHelper.buildModExpression(result, e);
                        break;
                }
            } catch (SLTranslationException e1) {
                throw new RuntimeException(e1);
            }
        }
        return result;
    }

    @Override
    public SLExpression visitUnaryexpr(JmlParser.UnaryexprContext ctx) {
        if (ctx.PLUS() != null) {
            SLExpression result = accept(ctx.unaryexpr());
            if (result.isType()) {
                raiseError("Cannot build  +" + result.getType().getName() + ".");
            }
            assert result.isTerm();
            try {
                return intHelper.buildPromotedUnaryPlusExpression(result);
            } catch (SLTranslationException e) {
                throw new RuntimeException(e);
            }
        }
        if (ctx.DECLITERAL() != null) {
            String text = ctx.getText();
            boolean isLong = text.endsWith("l") || text.endsWith("L");
            try {
                Literal literal = isLong ? new LongLiteral(text) : new IntLiteral(text);
                Term intLit =
                        services.getTypeConverter().getIntegerLDT().translateLiteral(literal, services);

                PrimitiveType literalType = isLong ? PrimitiveType.JAVA_LONG : PrimitiveType.JAVA_INT;
                return new SLExpression(intLit, javaInfo.getPrimitiveKeYJavaType(literalType));
            } catch (NumberFormatException e) {
                throw new RuntimeException(getExceptionManager().createException(e.getMessage(), e));
            }
        }
        if (ctx.MINUS() != null) {
            SLExpression result = accept(ctx.unaryexpr());
            if (result.isType()) {
                raiseError("Cannot build  -" + result.getType().getName() + ".");
            }
            assert result.isTerm();
            try {
                return intHelper.buildUnaryMinusExpression(result);
            } catch (SLTranslationException e) {
                throw new RuntimeException(e);
            }
        }
        return oneOf(ctx.castexpr(), ctx.unaryexprnotplusminus());
    }

    private <T> @Nullable T oneOf(ParserRuleContext @Nullable ... contexts) {
        for (ParserRuleContext context : contexts) {
            T t = accept(context);
            if (t != null) return t;
        }
        return null;
    }

    @Override
    public SLExpression visitCastexpr(JmlParser.CastexprContext ctx) {
        KeYJavaType type = null;
        Object rtype = accept(ctx.typespec());
        Object result = accept(ctx.unaryexpr());
        return translator.get(JMLTranslator.JMLKeyWord.CAST.toString(), services, intHelper, rtype, result);
    }


    @Override
    public Object visitUnaryexprnotplusminus(JmlParser.UnaryexprnotplusminusContext ctx) {
        if (ctx.NOT() != null) {
            SLExpression e = accept(ctx.unaryexpr());
            if (e.isType()) raiseError("Cannot negate type " + e.getType().getName() + ".");
            Term t = e.getTerm();
            if (t.sort() == Sort.FORMULA) {
                return new SLExpression(tb.not(t));
            } else if (t.sort() == booleanLDT.targetSort()) {
                return new SLExpression(tb.not(tb.equals(t, tb.TRUE())));
            } else {
                raiseError("Wrong type in not-expression: " + t);
            }
        }

        if (ctx.BITWISENOT() != null) {
            SLExpression e = accept(ctx.unaryexpr());
            if (e.isType()) raiseError("Cannot negate type " + e.getType().getName() + ".");
            try {
                return intHelper.buildPromotedNegExpression(e);
            } catch (SLTranslationException e1) {
                throw new RuntimeException(e1);
            }
        }
        return accept(ctx.postfixexpr());
    }

    @Override
    public SLExpression visitPostfixexpr(JmlParser.PostfixexprContext ctx) {
        fullyQualifiedName = "";
        SLExpression expr = accept(ctx.primaryexpr());

        if (expr != null && expr.getType() == null) {
            raiseError("SLExpression without a type: " + expr);
        }/* else if (expr != null && expr.getType().getJavaType() instanceof PrimitiveType) {
                raiseError("Cannot build postfix expression from primitive type.");
            }*/
        //TODO suffixes
        for (JmlParser.PrimarysuffixContext c : ctx.primarysuffix()) {
            receiver = expr;
            expr = accept(c);
            //fullyQualifiedName += "." + input.LT(-1).getText();
        }
        if (expr == null) {
            raiseError("Expression " + fullyQualifiedName + " cannot be resolved.");
        }
        return expr;
    }

    @Override
    public Object visitIdent(JmlParser.IdentContext ctx) {
        return lookupIdentifier(ctx.IDENT().getText(), null, null, ctx.IDENT().getSymbol());
    }

    @Override
    public Object visitInv(JmlParser.InvContext ctx) {
        return translator.get(ctx.INV().getText(), services,
                selfVar == null ? null : tb.var(selfVar), containerType);
    }

    @Override
    public Object visitTrue_(JmlParser.True_Context ctx) {
        return new SLExpression(tb.tt());
    }

    @Override
    public Object visitFalse_(JmlParser.False_Context ctx) {
        return new SLExpression(tb.ff());
    }

    @Override
    public Object visitNull_(JmlParser.Null_Context ctx) {
        return new SLExpression(tb.NULL());
    }

    @Override
    public Object visitThis_(JmlParser.This_Context ctx) {
        if (selfVar == null) {
            raiseError("Cannot access \"this\" in a static context!");
        }
        return new SLExpression(tb.var(selfVar), selfVar.getKeYJavaType());
    }

    private SLExpression lookupIdentifier(String lookupName,
                                          SLExpression receiver,
                                          SLParameters params,
                                          Token t) {

        // Identifier with suffix in parentheses? Probably a method call
        // parse in the parameter list and call again
        //if (input.LA(1) == LPAREN) {
        //    return receiver;
        //}

        SLExpression result = null;
        try {
            result = resolverManager.resolve(receiver,
                    lookupName,
                    params);
        } catch (SLTranslationException exc) {
            // no type name found maybe package?
        }

        if (result != null) {
            return result;
        }

        // no identifier found, maybe it was just a package prefix.
        // but package prefixes don't have a receiver!
        // Let primarysuffix handle faulty method call.
        if (receiver != null && params == null) {
            raiseError("Identifier " + lookupName + " not found: " +
                    lookupName);
        }

        return null;
    }

    //region suffix
    private SLExpression receiver;
    private String fullyQualifiedName;

    @Override
    public SLExpression visitPrimarySuffixAccess(JmlParser.PrimarySuffixAccessContext ctx) {
        String lookupName = null;
        lookupName = fullyQualifiedName;
        if (ctx.IDENT() != null) {
            String id = ctx.IDENT().getText();
            if (receiver == null) {
                // Receiver was only a package/classname prefix
                lookupName = fullyQualifiedName + "." + id;
            } else {
                lookupName = id;
            }
            try {
                return lookupIdentifier(lookupName, receiver, null, ctx.IDENT().getSymbol());
            } catch (Exception e) {
                return lookupIdentifier(fullyQualifiedName + "." + lookupName, null, null,
                        ctx.IDENT().getSymbol());
            }
        }
        if (ctx.TRANSIENT() != null) {
            return lookupIdentifier("<transient>", receiver, null, ctx.TRANSIENT().getSymbol());
        }
        if (ctx.THIS() != null) {
            return new SLExpression(
                    services.getTypeConverter().findThisForSort(receiver.getType().getSort(),
                            tb.var(selfVar),
                            javaInfo.getKeYJavaType(selfVar.sort()),
                            true),
                    receiver.getType());
        }
        if (ctx.INV() != null) {
            return translator.get("\\inv", services, receiver.getTerm(), receiver.getType());
        }
        if (ctx.MULT() != null) {
            return new SLExpression(tb.allFields(receiver.getTerm()),
                    javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }
        assert false;
        return null;
    }

    @Override
    public Object visitPrimarySuffixCall(JmlParser.PrimarySuffixCallContext ctx) {
        String lookupName = fullyQualifiedName;
        ImmutableList<SLExpression> params = accept(ctx.expressionlist());
        ImmutableList<SLExpression> preHeapParams = ImmutableSLList.nil();
        for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
            Term p;
            if (atPres == null || atPres.get(heap) == null) {
                p = tb.var(heap);
            } else {
                p = atPres.get(heap);
            }
            preHeapParams = preHeapParams.append(new SLExpression(p));
        }
        params = (params == null) ? preHeapParams : params.prepend(preHeapParams);
        lookupName = lookupName.substring(lookupName.lastIndexOf('.') + 1);
        SLExpression result = lookupIdentifier(lookupName, receiver, new SLParameters(params), ctx.LPAREN().getSymbol());
        if (result == null) {
            raiseError("Method " + lookupName + "("
                    + createSignatureString(params) + ") not found!", ctx.LPAREN().getSymbol());
        }
        if (((IProgramMethod) result.getTerm().op()).getStateCount() > 1
                && (atPres == null || atPres.get(getBaseHeap()) == null)) {
            raiseError("Two-state model method " + lookupName + " not allowed in this context!", ctx.LPAREN().getSymbol());
        }
        return result;
    }

    @Override
    public Object visitPrimarySuffixArray(JmlParser.PrimarySuffixArrayContext ctx) {
        Object rangeFrom = accept(ctx.from);
        Object rangeTo = accept(ctx.to);
        //TODO not handled by code ctx.MULT()
        return translator.get("array reference", services,
                receiver, fullyQualifiedName, ctx.LBRACKET(), rangeFrom, rangeTo);
    }
    //endregion

    @Override
    public Object visitNew_expr(JmlParser.New_exprContext ctx) {
        raiseNotSupported("'new' within specifications");
        return null;
    }

    @Override
    public Object visitArray_initializer(JmlParser.Array_initializerContext ctx) {
        raiseNotSupported("array initializer");
        return null;
    }

    @Override
    public ImmutableList<SLExpression> visitExpressionlist(JmlParser.ExpressionlistContext ctx) {
        return listOf(ctx.expression());
    }

    @Override
    public SLExpression visitStringliteral(JmlParser.StringliteralContext ctx) {
        Token l = ctx.STRING_LITERAL().getSymbol();
        Term charListTerm = services.getTypeConverter()
                .convertToLogicElement(new StringLiteral(l.getText()));
        Function strPool
                = services.getNamespaces()
                .functions()
                .lookup(CharListLDT.STRINGPOOL_NAME);
        if (strPool == null) {
            raiseError("string literals used in specification, "
                    + "but string pool function not found");
        }
        Term stringTerm = tb.func(strPool, charListTerm);
        return new SLExpression(stringTerm,
                javaInfo.getKeYJavaType("java.lang.String"));
    }

    @Override
    public SLExpression visitCharliteral(JmlParser.CharliteralContext ctx) {
        Term charLit = services.getTypeConverter().getIntegerLDT()
                .translateLiteral(new CharLiteral(ctx.getText()), services);
        return new SLExpression(charLit, javaInfo.getKeYJavaType("char"));
    }


    @Override
    public SLExpression visitIntegerliteral(JmlParser.IntegerliteralContext ctx) {
        SLExpression result;
        int radix = 10;
        if (ctx.HEXLITERAL() != null) {
            radix = 16;
        }
        if (ctx.OCTLITERAL() != null) {
            radix = 8;
        }
        if (ctx.BINLITERAL() != null) {
            radix = 2;
        }
        String text = ctx.getText();
        boolean isLong = text.endsWith("l") || text.endsWith("L");
        try {
            Literal literal = isLong ? new LongLiteral(text) : new IntLiteral(text);
            Term intLit = services.getTypeConverter().getIntegerLDT().translateLiteral(literal, services);
            PrimitiveType literalType = isLong ? PrimitiveType.JAVA_LONG : PrimitiveType.JAVA_INT;
            result = new SLExpression(intLit, javaInfo.getPrimitiveKeYJavaType(literalType));
        } catch (NumberFormatException e) {
            throw new RuntimeException(getExceptionManager().createException(e.getMessage(), e));
        }
        return result;
    }


    @Override
    public Object visitPrimaryResult(JmlParser.PrimaryResultContext ctx) {
        if (resultVar == null) {
            raiseError("\\result used in wrong context");
        }
        return new SLExpression(tb.var(resultVar), resultVar.getKeYJavaType());
    }

    @Override
    public Object visitPrimaryException(JmlParser.PrimaryExceptionContext ctx) {
        if (excVar == null) raiseError("\\exception may only appear in determines clauses");
        return new SLExpression(tb.var(excVar), excVar.getKeYJavaType());
    }

    @Override
    public Object visitPrimaryBackup(JmlParser.PrimaryBackupContext ctx) {
        SLExpression result = accept(ctx.expression());
        if (atPres == null || atPres.get(getSavedHeap()) == null) {
            raiseError("JML construct " +
                    "\\backup not allowed in this context.");
        }
        Object typ = result.getType();
        if (typ != null) {
            result = new SLExpression(convertToBackup(result.getTerm()),
                    result.getType());
        } else {
            result = new SLExpression(convertToBackup(result.getTerm()));
        }
        return result;
    }

    @Override
    public Object visitPrimaryPermission(JmlParser.PrimaryPermissionContext ctx) {
        return new SLExpression(convertToPermission(((SLExpression) accept(ctx.expression())).getTerm()));
    }

    @Override
    public Object visitPrimaryNNE(JmlParser.PrimaryNNEContext ctx) {
        SLExpression result = accept(ctx.expression());
        Term t = result.getTerm();
        Term resTerm = tb.not(tb.equals(t, tb.NULL()));
        if (t.sort() instanceof ArraySort) {
            LogicVariable i =
                    new LogicVariable(new Name("i"),
                            javaInfo
                                    .getKeYJavaType(PrimitiveType.JAVA_INT)
                                    .getSort());

            // See JML reference manual
            // http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139
            Term range = tb.and(tb.leq(tb.zero(), tb.var(i)),
                    tb.lt(tb.var(i), tb.dotLength(t)));
            Term body = tb.equals(tb.dotArr(t, tb.var(i)), tb.NULL());
            body = tb.not(body);
            body = tb.imp(range, body);

            result = new SLExpression(tb.and(resTerm, tb.all(i, body)));
        } else {
            raiseError("\\nonnullelements may only be applied to arrays");
        }
        return result;
    }

    @Override
    public SLExpression visitPrimaryInformalDesc(JmlParser.PrimaryInformalDescContext ctx) {
        return translator.get("(* *)", services, ctx.INFORMAL_DESCRIPTION().getText(),
                selfVar, resultVar, paramVars, atPres == null ? null : atPres.get(getBaseHeap()));
    }

    @Override
    public Object visitPrimaryDLCall(JmlParser.PrimaryDLCallContext ctx) {
        Object escape = ctx.DL_ESCAPE().getText();
        Object list = accept(ctx.expressionlist());
        return translator.get("\\dl_", escape, list, services);
    }

    @Override
    public Object visitPrimaryMapEmpty(JmlParser.PrimaryMapEmptyContext ctx) {
        return translator.translateMapExpressionToJDL(ctx.MAPEMPTY().getText(), null/*?*/, services);
    }

    @Override
    public SLExpression visitPrimaryMapExpr(JmlParser.PrimaryMapExprContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        Token tk = ctx.mapExpression().getStart();
        return translator.translateMapExpressionToJDL(tk.getText(), list, services);
    }

    @Override
    public SLExpression visitPrimarySeq2Map(JmlParser.PrimarySeq2MapContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        return translator.translateMapExpressionToJDL(ctx.SEQ2MAP().getText(), list, services);
    }


    @Override
    public Object visitPrimaryNotMod(JmlParser.PrimaryNotModContext ctx) {
        SLExpression t = accept(ctx.storeRefUnion());
        //TODO atPres
        final Term a = translator.get("\\not_modified",
                services, atPres == null ? null : atPres.get(getBaseHeap()), t);
        return new SLExpression(a);
    }

    @Override
    public Object visitPrimaryNotAssigned(JmlParser.PrimaryNotAssignedContext ctx) {
        return translator.createSkolemExprBool(ctx.NOT_ASSIGNED().getText());
    }

    @Override
    public Object visitPrimaryFresh(JmlParser.PrimaryFreshContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        return translator.get("\\fresh", SLExpression.class, list, atPres, services);
    }

    @Override
    public SLExpression visitPrimaryReach(JmlParser.PrimaryReachContext ctx) {
        Term t = accept(ctx.storeref());
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = ctx.expression().size() == 3 ? accept(ctx.expression(2)) : null;
        return translator.get("reach", t, e1, e2, e3, services);
    }

    @Override
    public SLExpression visitPrimaryReachLocs(JmlParser.PrimaryReachLocsContext ctx) {
        Term t = accept(ctx.storeref());
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e3 = ctx.expression().size() == 2 ? accept(ctx.expression(1)) : null;
        return translator.get("reachLocs", t, e1, e3, services);
    }


    @Override
    public Object visitPrimaryDuration(JmlParser.PrimaryDurationContext ctx) {
        return translator.createSkolemExprLong(ctx.DURATION().getText(), services);
    }

    @Override
    public Object visitPrimarySpace(JmlParser.PrimarySpaceContext ctx) {
        //TODO expression ignored
        return translator.createSkolemExprLong(ctx.SPACE().getText(), services);
    }

    @Override
    public Object visitPrimaryWorksingSpace(JmlParser.PrimaryWorksingSpaceContext ctx) {
        //TODO expression ignored
        return translator.createSkolemExprLong(ctx.WORKINGSPACE().getText(), services);
    }

    @Override
    public Object visitPrimaryParen(JmlParser.PrimaryParenContext ctx) {
        return accept(ctx.expression());
    }

    /*TODO missing in grammar
    |   (MAX) => max=MAX LPAREN result=expression RPAREN
    {
        return  translator.createSkolemExprObject(max,services);
    }*/

    @Override
    public Object visitPrimaryTypeOf(JmlParser.PrimaryTypeOfContext ctx) {
        SLExpression result = accept(ctx.expression());
        return new SLExpression(result.getTerm(),
                result.getType(),
                false);
    }

    @Override
    public Object visitPrimaryElemtype(JmlParser.PrimaryElemtypeContext ctx) {
        raiseNotSupported(ctx.ELEMTYPE());
        return null;
    }


    @Override
    public Object visitPrimayTypeSpec(JmlParser.PrimayTypeSpecContext ctx) {
        KeYJavaType typ = accept(ctx.typespec());
        return new SLExpression(typ);
    }

    @Override
    public Object visitPrimaryLockset(JmlParser.PrimaryLocksetContext ctx) {
        return translator.createSkolemExprObject(ctx.LOCKSET().getText(), services);
    }

    @Override
    public Object visitPrimaryIsInitialised(JmlParser.PrimaryIsInitialisedContext ctx) {
        KeYJavaType typ = accept(ctx.referencetype());
        Term resTerm = tb.equals(tb.var(
                javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, typ)),
                tb.TRUE());
        return new SLExpression(resTerm);
    }

    @Override
    public SLExpression visitPrimaryInvFor(JmlParser.PrimaryInvForContext ctx) {
        Object result = accept(ctx.expression());
        return translator.get("\\invariant_for", services, result);
    }

    @Override
    public SLExpression visitPrimaryStaticInv(JmlParser.PrimaryStaticInvContext ctx) {
        Object typ = accept(ctx.referencetype());
        return translator.get("\\static_invariant_for", services, typ);
    }

    @Override
    public Object visitPrimaryLblNeg(JmlParser.PrimaryLblNegContext ctx) {
        addIgnoreWarning("\\lblneg", ctx.LBLNEG().getSymbol());
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryLblPos(JmlParser.PrimaryLblPosContext ctx) {
        addIgnoreWarning("\\lblpos", ctx.LBLPOS().getSymbol());
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryIndex(JmlParser.PrimaryIndexContext ctx) {
        return translator.get(JMLTranslator.JMLKeyWord.INDEX.toString(), services);
    }

    @Override
    public Object visitPrimaryValues(JmlParser.PrimaryValuesContext ctx) {
        return translator.get(JMLTranslator.JMLKeyWord.VALUES.toString(), services);
    }

    @Override
    public Object visitPrimaryStringEq(JmlParser.PrimaryStringEqContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        Function strContent = services.getNamespaces().functions().lookup(CharListLDT.STRINGCONTENT_NAME);
        if (strContent == null) {
            raiseError("strings used in spec, but string content function not found");
        }
        return new SLExpression(tb.equals(tb.func(strContent, e1.getTerm()), tb.func(strContent, e2.getTerm())));
    }

    @Override
    public Object visitPrimaryEmptySet(JmlParser.PrimaryEmptySetContext ctx) {
        return translator.get(JMLTranslator.JMLKeyWord.EMPTY.toString(), services, javaInfo);
    }

    @Override
    public Object visitPrimaryignor9(JmlParser.Primaryignor9Context ctx) {
        Term t = accept(ctx.createLocset());
        return new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryUnion(JmlParser.PrimaryUnionContext ctx) {
        KeYJavaType t = accept(ctx.storeRefUnion());
        return translator.get(JMLTranslator.JMLKeyWord.UNION.toString(), t, javaInfo);
    }

    @Override
    public Object visitPrimaryIntersect(JmlParser.PrimaryIntersectContext ctx) {
        Object t = accept(ctx.storeRefIntersect());
        return translator.get(JMLTranslator.JMLKeyWord.INTERSECT.toString(), t, javaInfo);
    }

    @Override
    public Object visitPrimarySetMinux(JmlParser.PrimarySetMinuxContext ctx) {
        Term t = accept(ctx.storeref(0));
        Term t2 = accept(ctx.storeref(1));
        return new SLExpression(tb.setMinus(t, t2),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryAllFields(JmlParser.PrimaryAllFieldsContext ctx) {
        SLExpression e1 = accept(ctx.expression());
        if (!e1.isTerm() || !e1.getTerm().sort().extendsTrans(services.getJavaInfo().objectSort())) {
            raiseError("Invalid argument to \\allFields: " + e1);
        }
        return new SLExpression(tb.allFields(e1.getTerm()),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryAllObj(JmlParser.PrimaryAllObjContext ctx) {
        Term t = accept(ctx.storeref());
        return new SLExpression(tb.allObjects(t.sub(1)),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryUnionInf(JmlParser.PrimaryUnionInfContext ctx) {
        System.err.println("!!! Deprecation Warnung: You used \\infinite_union in the functional syntax \\infinite_union(...)."
                + "\n\tThis is deprecated and won't be valid in future versions of KeY."
                + "\n\tPlease use \\infinite_union as a binder instead: (\\infinite_union var type; guard; store-ref-expr).");

        Object nullable = accept(ctx.boundvarmodifiers());
        @Nullable Pair<KeYJavaType, ProgramVariable> declVars = accept(ctx.quantifiedvardecls());
        if (declVars != null) {
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
        }
        Term t2 = accept(ctx.predicate());
        Term t = accept(ctx.storeref());
        if (declVars != null) resolverManager.popLocalVariablesNamespace();
        return translator.get(JMLTranslator.JMLKeyWord.UNIONINF.toString(), nullable, declVars, t, t2, services);
    }

    @Override
    public SLExpression visitPrimaryDisjoint(JmlParser.PrimaryDisjointContext ctx) {
        ImmutableList<SLExpression> tlist = accept(ctx.storeRefList());
        return translator.get(ctx.DISJOINT().getText(), tlist, services);
    }

    @Override
    public SLExpression visitPrimarySubset(JmlParser.PrimarySubsetContext ctx) {
        Term t = accept(ctx.storeref(0));
        Term t2 = accept(ctx.storeref(1));
        return new SLExpression(tb.subset(t, t2));
    }

    @Override
    public SLExpression visitPrimaryNewElemsfrehs(JmlParser.PrimaryNewElemsfrehsContext ctx) {
        Term t = accept(ctx.storeref());
        return new SLExpression(tb.subset(t,
                tb.union(convertToOld(t),
                        tb.freshLocs(atPres == null ? null : atPres.get(getBaseHeap())))));
    }

    @Override
    public Object visitPrimaryignore10(JmlParser.Primaryignore10Context ctx) {
        return super.visitPrimaryignore10(ctx);
    }

    @Override
    public SLExpression visitSequenceEmpty(JmlParser.SequenceEmptyContext ctx) {
        return new SLExpression(tb.seqEmpty());
    }

    @Override
    public SLExpression visitSequenceCreate(JmlParser.SequenceCreateContext ctx) {
        Object list = accept(ctx.exprList());
        return translator.get("\\seq", list, services);
    }

    @Override
    public Object visitSequenceSub(JmlParser.SequenceSubContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = accept(ctx.expression(2));
        return new SLExpression(tb.seqSub(e1.getTerm(), e2.getTerm(), e3.getTerm()));
    }

    @Override
    public Object visitSequenceReverse(JmlParser.SequenceReverseContext ctx) {
        SLExpression e1 = accept(ctx.expression());
        return new SLExpression(tb.seqReverse(e1.getTerm()));
    }

    @Override
    public Object visitSequenceReplace(JmlParser.SequenceReplaceContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = accept(ctx.expression(2));
        // short for "e1[0..e2-1]+e3+e1[e2+1..e1.length-1]"
        final Term minusOne = tb.zTerm("-1");
        final Term ante = tb.seqSub(e1.getTerm(), tb.zero(), tb.add(e2.getTerm(), minusOne));
        final Term insert = tb.seqSingleton(e3.getTerm());
        final Term post = tb.seqSub(e1.getTerm(), tb.add(e2.getTerm(), tb.one()), tb.add(tb.seqLen(e1.getTerm()), minusOne));
        final Term put = tb.seqConcat(ante, tb.seqConcat(insert, post));
        return new SLExpression(put);
    }

    @Override
    public Object visitSequenceFuncs(JmlParser.SequenceFuncsContext ctx) {
        String op = ctx.op.getText();
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        return translator.get(op, services, e1, e2);
    }

    @Override
    public Object visitInfinite_union_expr(JmlParser.Infinite_union_exprContext ctx) {
        Object nullable = accept(ctx.boundvarmodifiers());
        @Nullable Pair<KeYJavaType, ProgramVariable> declVars = accept(ctx.quantifiedvardecls());
        if (declVars != null) {
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
        }
        Term t2 = accept(ctx.predicate());
        Term t = accept(ctx.storeref());
        if (declVars != null) resolverManager.popLocalVariablesNamespace();
        return translator.get(JMLTranslator.JMLKeyWord.UNIONINF.toString(), nullable, declVars, t, t2, services);
    }

    @Override
    public SLExpression visitSpecquantifiedexpression(JmlParser.SpecquantifiedexpressionContext ctx) {
        Term p = tb.tt();
        Object nullable = accept(ctx.boundvarmodifiers());
        String q = ctx.quantifier().start.getText();
        Pair<KeYJavaType, ProgramVariable> declVars = accept(ctx.quantifiedvardecls());
        {
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
        }
        if (ctx.predicate() != null)
            p = accept(ctx.predicate());
        SLExpression expr = accept(ctx.expression());
        resolverManager.popLocalVariablesNamespace();
        p = tb.convertToFormula(p);
        return translator.get(q, p, expr.getTerm(),
                declVars.first, declVars.second,
                nullable, expr.getType(), services);
    }

    @Override
    public SLExpression visitOldexpression(JmlParser.OldexpressionContext ctx) {
        KeYJavaType typ;
        SLExpression result = accept(ctx.expression());
        @Nullable String id = accept(ctx.IDENT());

        if (atPres == null || atPres.get(getBaseHeap()) == null) {
            raiseError("JML construct " +
                    "\\old not allowed in this context.");
        }

        if (ctx.IDENT() != null) addIgnoreWarning("\\old with label ", ctx.IDENT().getSymbol());
        typ = result.getType();
        if (typ != null) {
            result = new SLExpression(convertToOld(result.getTerm()),
                    result.getType());
        } else {
            result = new SLExpression(convertToOld(result.getTerm()));
        }
        return result;
    }

    @Override
    public SLExpression visitBeforeexpression(JmlParser.BeforeexpressionContext ctx) {
        KeYJavaType typ;
        SLExpression result = accept(ctx.expression());
        if (atBefores == null || atBefores.get(getBaseHeap()) == null) {
            raiseError("JML construct " +
                    "\\before not allowed in this context.");
        }

        typ = result.getType();
        if (typ != null) {
            result = new SLExpression(convertToBefore(result.getTerm()),
                    result.getType());
        } else {
            result = new SLExpression(convertToBefore(result.getTerm()));
        }
        return result;
    }

    @Override
    public SLExpression visitBsumterm(JmlParser.BsumtermContext ctx) {
        @Nullable Pair<KeYJavaType, ProgramVariable> decls = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        SLExpression a = accept(ctx.expression(0));
        SLExpression b = accept(ctx.expression(1));
        SLExpression t = accept(ctx.expression(2));
        SLExpression result = translator.get(ctx.BSUM().getText(), a, b, t, decls.first, decls.second, services);
        resolverManager.popLocalVariablesNamespace();
        return result;
    }

    @Override
    public Object visitSeqdefterm(JmlParser.SeqdeftermContext ctx) {
        @Nullable Pair<KeYJavaType, ProgramVariable> decls = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        SLExpression a = accept(ctx.expression(0));
        SLExpression b = accept(ctx.expression(1));
        SLExpression t = accept(ctx.expression(2));
        SLExpression result = translator.get(ctx.SEQDEF().getText(), a, b, t, decls.first, decls.second, services);
        resolverManager.popLocalVariablesNamespace();
        return result;
    }

    @Override
    public Pair<KeYJavaType, ImmutableList<LogicVariable>> visitQuantifiedvardecls(JmlParser.QuantifiedvardeclsContext ctx) {
        Pair<KeYJavaType, ImmutableList<LogicVariable>> result = null;
        ImmutableList<LogicVariable> vars = ImmutableSLList.nil();
        KeYJavaType t = accept(ctx.typespec());
        for (JmlParser.QuantifiedvariabledeclaratorContext context : ctx.quantifiedvariabledeclarator()) {
            LogicVariable v = visitQuantifiedvariabledeclarator(context, t);
            vars = vars.append(v);
        }
        return new Pair<>(t, vars);
    }

    @Override
    public Boolean visitBoundvarmodifiers(JmlParser.BoundvarmodifiersContext ctx) {
        return ctx.NULLABLE() != null;
    }

    @Override
    public KeYJavaType visitTypespec(JmlParser.TypespecContext ctx) {
        KeYJavaType t = accept(ctx.type());
        String fullName = t.getFullName() + (ctx.dims() != null ? ctx.dims().getText() : "");
        t = javaInfo.getKeYJavaType(fullName);
        if (t == null && ctx.dims() != null) {
            //try to create missing array type
            try {
                javaInfo.readJavaBlock("{" + fullName + " k;}");
                t = javaInfo.getKeYJavaType(fullName);
            } catch (Exception e) {
                t = null;
            }
        }
        return t;
    }

    @Override
    public Object visitDims(JmlParser.DimsContext ctx) {
        return ctx.LBRACKET().size();
    }

    @Override
    public KeYJavaType visitType(JmlParser.TypeContext ctx) {
        if (ctx.TYPE() != null) {
            raiseNotSupported("\\TYPE");
        }
        return oneOf(ctx.builtintype(), ctx.referencetype());
    }

    @Override
    public KeYJavaType visitReferencetype(JmlParser.ReferencetypeContext ctx) {
        String typename = accept(ctx.name());
        try {
            return resolverManager.resolve(null, typename, null).getType();
        } catch (NullPointerException e) {
            raiseError("Type " + typename + " not found.");
        } catch (SLTranslationException e) {
            throw new RuntimeException(e);
        }
        return null;
    }

    @Override
    public String visitName(JmlParser.NameContext ctx) {
        return ctx.getText();
    }

    @Override
    public Object visitQuantifiedvariabledeclarator(JmlParser.QuantifiedvariabledeclaratorContext ctx) {
        throw new IllegalArgumentException("call the other method");
    }

    public LogicVariable visitQuantifiedvariabledeclarator(JmlParser.QuantifiedvariabledeclaratorContext ctx, KeYJavaType t) {
        LogicVariable v = null;
        KeYJavaType varType = null;
        int dim = ctx.dims() == null ? 0 : accept(ctx.dims());
        String id = ctx.IDENT().toString();
        if (dim > 0) {
            String fullName;
            if (t.getJavaType() instanceof ArrayType) {
                fullName = ((ArrayType) t.getJavaType()).getAlternativeNameRepresentation();
            } else {
                fullName = t.getFullName();
            }
            for (int i = 0; i < dim; i++) {
                fullName += "[]";
            }
            varType = javaInfo.getKeYJavaType(fullName);
        } else {
            varType = t;
        }
        return new LogicVariable(new Name(id), varType.getSort());
    }

    private void raiseNotSupported(String feature) {
        throw new RuntimeException(excManager.createWarningException(feature + " not supported"));
    }

    private void raiseNotSupported(TerminalNode elemtype) {
        throw new RuntimeException(excManager.createWarningException(elemtype.getText() + " not supported"));
    }
}