package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Label;
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
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.translation.JMLResolverManager;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.*;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jetbrains.annotations.Contract;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.*;
import java.util.stream.Collectors;

import static de.uka.ilkd.key.speclang.njml.JmlFacade.TODO;
import static java.lang.String.format;
import static java.util.Objects.requireNonNull;

/**
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
@SuppressWarnings("unchecked")
class Translator extends JmlParserBaseVisitor<Object> {
    private final Services services;
    private final TermBuilder tb;
    private final JavaInfo javaInfo;
    private final KeYJavaType containerType;
    private final IntegerLDT intLDT;
    private final HeapLDT heapLDT;
    private final LocSetLDT locSetLDT;
    private final BooleanLDT booleanLDT;
    private final SLExceptionFactory exc;
    private final JmlTermFactory translator;
    private final ProgramVariable selfVar;
    private final ImmutableList<ProgramVariable> paramVars;
    private final ProgramVariable resultVar;
    private final ProgramVariable excVar;
    private final Map<LocationVariable, Term> atPres;
    private final Map<LocationVariable, Term> atBefores;

    // Helper objects
    private final JMLResolverManager resolverManager;
    private final JavaIntegerSemanticsHelper intHelper;

    Translator(Services services,
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
        this.exc = new SLExceptionFactory("", 0, 0, 0);

        this.selfVar = self;
        this.paramVars = paramVars;
        this.resultVar = result;
        this.excVar = exc;
        this.atPres = atPres;
        this.atBefores = atBefores;

        intHelper = new JavaIntegerSemanticsHelper(services, this.exc);
        this.translator = new JmlTermFactory(this.exc, services, intHelper);
        // initialize helper objects
        this.resolverManager = new JMLResolverManager(this.javaInfo,
                specInClass, selfVar, this.exc);

        // initialize namespaces
        resolverManager.pushLocalVariablesNamespace();
        if (paramVars != null) {
            resolverManager.putIntoTopLocalVariablesNamespace(paramVars);
        }
        if (resultVar != null) {
            resolverManager.putIntoTopLocalVariablesNamespace(resultVar);
        }
    }

    /*private void raiseError(String msg, Token t)
            throws SLTranslationException {
        throw excManager.createException(msg, t);
    }

    private void raiseNotSupported(String feature)
            throws SLTranslationException {
        throw excManager.createWarningException(feature + " not supported");
    }*/


    //region accept helpers
    @Contract("null -> null")
    private <T> @Nullable T accept(@Nullable ParserRuleContext ctx) {
        if (ctx == null) return null;
        return (T) ctx.accept(this);
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

    private <T> @Nullable T oneOf(ParserRuleContext @Nullable ... contexts) {
        for (ParserRuleContext context : requireNonNull(contexts)) {
            T t = accept(context);
            if (t != null) return t;
        }
        return null;
    }
    //endregion

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
        Map<Term, Term> map = new LinkedHashMap<>();
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
        Map<Term, Term> map = new LinkedHashMap<>();
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
        Map<Term, Term> map = new LinkedHashMap<>();
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
        StringBuilder sigString = new StringBuilder();

        for (SLExpression expr : signature) {
            final KeYJavaType t = expr.getType();
            sigString.append(t == null ? "<unknown type>" : t.getFullName()).append(", ");
        }

        return sigString.substring(0, sigString.length() - 2);
    }

    //region expression

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
        throw new IllegalArgumentException();
    }


    private <T> ImmutableList<T> append(ImmutableList<T> by, ParserRuleContext ctx) {
        return by.append((T) accept(ctx));
    }

    private ImmutableList<Term> append(ImmutableList<Term> target,
                                       List<JmlParser.InfflowspeclistContext> ctx) {
        for (ParserRuleContext c : ctx) {
            ImmutableList<Term> t = accept(c);
            target = target.append(t);
        }
        return target;
    }

    private @Nullable String accept(@Nullable TerminalNode ident) {
        if (ident == null) return null;
        return ident.getText();
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
    public Term visitTermexpression(JmlParser.TermexpressionContext ctx) {
        return ((SLExpression) requireNonNull(accept(ctx.expression()))).getTerm();
    }

    @Override
    public Object visitStoreRefUnion(JmlParser.StoreRefUnionContext ctx) {
        return tb.union((Iterable<Term>) requireNonNull(accept(ctx.storeRefList())));
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
        return tb.intersect((Iterable<Term>) requireNonNull(accept(ctx.storeRefList())));
    }

    @Override
    public Object visitStoreref(JmlParser.StorerefContext ctx) {
        if (null != ctx.NOTHING()) return tb.empty();
        if (null != ctx.EVERYTHING()) return tb.createdLocs();
        if (null != ctx.NOT_SPECIFIED()) return tb.createdLocs();
        if (null != ctx.STRICTLY_NOTHING()) return tb.strictlyNothing();
        else
            return accept(ctx.storeRefExpr());
    }

    @Override
    public Object visitCreateLocset(JmlParser.CreateLocsetContext ctx) {
        //TODO? (LOCSET | SINGLETON)
        return translator.createLocSet(requireNonNull(accept(ctx.exprList())));
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
    public Term visitStoreRefExpr(JmlParser.StoreRefExprContext ctx) {
        return translator.createStoreRef(requireNonNull(accept(ctx.expression())));
    }


    @Override
    public SLExpression visitPredornot(JmlParser.PredornotContext ctx) {
        if (ctx.predicate() != null) return accept(ctx.predicate());
        if (ctx.NOT_SPECIFIED() != null)
            return new SLExpression(translator.createSkolemExprBool(ctx.NOT_SPECIFIED().getText()).getTerm());
        if (ctx.SAME() != null) {
            return null; //TODO check
        }
        throw new IllegalArgumentException();
    }

    @Override
    public Object visitPredicate(JmlParser.PredicateContext ctx) {
        SLExpression expr = accept(ctx.expression());
        assert expr != null;
        if (!expr.isTerm() && expr.getTerm().sort() == Sort.FORMULA) {
            raiseError("Expected a formula: " + expr);
        }
        return expr;
    }

    @Override
    public SLExpression visitExpression(JmlParser.ExpressionContext ctx) {
        SLExpression result = accept(ctx.conditionalexpr());
        assert result != null;
        if (!result.isTerm()) {
            raiseError("Expected a term: " + result);
        }
        return result;
    }

    @Override
    public SLExpression visitConditionalexpr(JmlParser.ConditionalexprContext ctx) {
        SLExpression cond = accept(ctx.equivalenceexpr());
        if (ctx.conditionalexpr().isEmpty()) return cond;
        SLExpression then = accept(ctx.conditionalexpr(0));
        SLExpression else_ = accept(ctx.conditionalexpr(1));
        assert else_ != null;
        assert then != null;
        assert cond != null;
        return translator.ite(cond, then, else_);
    }

    @Override
    public Object visitEquivalenceexpr(JmlParser.EquivalenceexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.impliesexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String op = ctx.EQV_ANTIV(i - 1).getText();
            SLExpression expr = e.get(i);
            if (op.equals("<==>"))
                result = translator.equivalence(result, expr);
            else
                result = translator.antivalence(result, expr);
        }
        return result;
    }

    /*
     * Note: According to JML Manual 12.6.3 forward implication has to be parsed right-associatively
     * and backward implication left-associatively.
     */
    @Override
    public Object visitImpliesexpr(JmlParser.ImpliesexprContext ctx) {
        SLExpression result = accept(ctx.a);
        if (ctx.IMPLIES() != null) {
            SLExpression expr = accept(ctx.b);
            assert expr != null;
            assert result != null;
            result = new SLExpression(tb.imp(tb.convertToFormula(result.getTerm()),
                    tb.convertToFormula(expr.getTerm())));
        }
        if (!ctx.IMPLIESBACKWARD().isEmpty()) {
            List<SLExpression> exprs = mapOf(ctx.c);
            for (SLExpression expr : exprs) {
                assert result != null;
                result = new SLExpression(tb.imp(tb.convertToFormula(expr.getTerm()),
                        tb.convertToFormula(result.getTerm())));
            }
        }
        assert result != null;
        return result;
    }

    @Override
    public SLExpression visitImpliesforwardexpr(JmlParser.ImpliesforwardexprContext ctx) {
        SLExpression result = accept(ctx.a);
        if (ctx.b != null) {
            SLExpression expr = accept(ctx.b);
            assert expr != null;
            assert result != null;
            return new SLExpression(tb.imp(tb.convertToFormula(result.getTerm()),
                    tb.convertToFormula(expr.getTerm())));
        }
        return result;
    }

    @Override
    public SLExpression visitLogicalorexpr(JmlParser.LogicalorexprContext ctx) {
        if (ctx.logicalandexpr().size() == 1) return accept(ctx.logicalandexpr(0));

        List<SLExpression> seq = mapOf(ctx.logicalandexpr());
        return seq.stream().reduce((a, b) ->
                new SLExpression(tb.orSC(tb.convertToFormula(a.getTerm()),
                        tb.convertToFormula(b.getTerm())))).orElse(null);
    }

    @Override
    public Object visitRelationalexpr(JmlParser.RelationalexprContext ctx) {
        return oneOf(ctx.shiftexpr(), ctx.instance_of(),
                ctx.relational_chain(), ctx.relational_lockset(), ctx.st_expr());
    }

    @Override
    public Object visitLogicalandexpr(JmlParser.LogicalandexprContext ctx) {
        if (ctx.inclusiveorexpr().size() == 1)
            return accept(ctx.inclusiveorexpr(0));

        List<SLExpression> seq = mapOf(ctx.inclusiveorexpr());
        return seq.stream().reduce((a, b) ->
                new SLExpression(tb.andSC(tb.convertToFormula(a.getTerm()),
                        tb.convertToFormula(b.getTerm())))).orElse(null);
    }

    @Override
    public Object visitInclusiveorexpr(JmlParser.InclusiveorexprContext ctx) {
        if (ctx.exclusiveorexpr().size() == 1) return accept(ctx.exclusiveorexpr(0));

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
        if (ctx.andexpr().size() == 1) return accept(ctx.andexpr(0));

        List<SLExpression> exprs = mapOf(ctx.andexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
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
        if (ctx.equalityexpr().size() == 1)
            return accept(ctx.equalityexpr(0));

        List<SLExpression> exprs = mapOf(ctx.equalityexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
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
            TerminalNode tok = ctx.EQ_NEQ(i - 1);
            if (tok.getText().equals("=="))
                result = translator.eq(result, expr.get(i));
            else
                result = translator.neq(result, expr.get(i));
        }
        return result;
    }

    @Override
    public SLExpression visitInstance_of(JmlParser.Instance_ofContext ctx) {
        SLExpression result = accept(ctx.shiftexpr());
        KeYJavaType rtype = accept(ctx.typespec());
        assert rtype != null;
        SortDependingFunction f = rtype.getSort().getInstanceofSymbol(services);
        // instanceof-expression
        assert result != null;
        return new SLExpression(
                tb.and(tb.not(tb.equals(result.getTerm(), tb.NULL())),
                        tb.equals(tb.func(f, result.getTerm()), tb.TRUE())));
    }

    @Override
    public Object visitSt_expr(JmlParser.St_exprContext ctx) {
        SLExpression result = accept(ctx.shiftexpr(0));
        SLExpression right = accept(ctx.shiftexpr(1));
        assert result != null && right != null;

        if (result.isTerm() || right.isTerm()) {
            raiseError("Cannot build subtype expression from terms.", ctx.ST().getSymbol());
        }
        assert result.isType();
        assert right.isType();
        if (result.getTerm() == null) {
            exc.addIgnoreWarning("subtype expression <: only supported for" +
                    " \\typeof() arguments on the left side.", ctx.ST().getSymbol());
            final Namespace<Function> fns = services.getNamespaces().functions();
            int x = -1;
            Name name;
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
            exc.addIgnoreWarning("Lockset ordering is not supported", ctx.LOCKSET_LEQ().getSymbol());
            final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
            f = new Function(new Name("lockset_leq"), Sort.FORMULA, objSort, objSort);
        }
        if (ctx.LOCKSET_LT() != null) {
            exc.addIgnoreWarning("Lockset ordering is not supported", ctx.LOCKSET_LT().getSymbol());
            final Sort objSort = services.getJavaInfo().getJavaLangObject().getSort();
            f = new Function(new Name("lockset_lt"), Sort.FORMULA, objSort, objSort);
        }
        assert f != null;
        assert right != null;
        assert left != null;
        return new SLExpression(tb.func(f, left.getTerm(), right.getTerm()));
    }

    @Override
    public SLExpression visitRelational_chain(JmlParser.Relational_chainContext ctx) {
        List<SLExpression> expressions = mapOf(ctx.shiftexpr());
        SLExpression result = null;
        for (int i = 1; i < expressions.size(); i++) {
            Function f = null;
            Token op = ctx.op.get(i - 1);
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

            SLExpression left = expressions.get(i - 1);
            SLExpression right = expressions.get(i);
            SLExpression rel = new SLExpression(tb.func(f, left.getTerm(), right.getTerm()));
            if (result == null) {
                result = rel;
            } else {
                result = new SLExpression(tb.and(result.getTerm(), rel.getTerm()));
            }
        }
        assert result != null;
        return result;
    }


    @Override
    public Object visitShiftexpr(JmlParser.ShiftexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.additiveexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String op = ctx.op.get(i - 1).getText();
            SLExpression expr = e.get(i);
            switch (op) {
                case "<<":
                    result = translator.shiftLeft(result, expr);
                    break;
                case ">>":
                    result = translator.shiftRight(result, expr);
                    break;
                case ">>>":
                    result = translator.unsignedShiftRight(result, expr);
                    break;
            }
        }
        return result;
    }

    @Override
    public Object visitAdditiveexpr(JmlParser.AdditiveexprContext ctx) {
        List<SLExpression> e = mapOf(ctx.multexpr());
        SLExpression result = e.get(0);
        for (int i = 1; i < e.size(); i++) {
            String op = ctx.op.get(i - 1).getText();
            SLExpression expr = e.get(i);
            if (op.equals("+"))
                result = translator.add(result, expr);
            else
                result = translator.substract(result, expr);
        }
        return result;
    }

    @Override
    public Object visitMultexpr(JmlParser.MultexprContext ctx) {
        List<SLExpression> exprs = mapOf(ctx.unaryexpr());
        SLExpression result = exprs.get(0);
        for (int i = 1; i < exprs.size(); i++) {
            Token op = ctx.op.get(i - 1);
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
            assert result != null;
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
                throw new RuntimeException(e.getMessage(), e);
            }
        }
        if (ctx.MINUS() != null) {
            SLExpression result = accept(ctx.unaryexpr());
            assert result != null;
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

    @Override
    public SLExpression visitCastexpr(JmlParser.CastexprContext ctx) {
        KeYJavaType rtype = accept(ctx.typespec());
        SLExpression result = accept(ctx.unaryexpr());
        return translator.cast(rtype, result);
    }

    @Override
    public Object visitUnaryexprnotplusminus(JmlParser.UnaryexprnotplusminusContext ctx) {
        if (ctx.NOT() != null) {
            SLExpression e = accept(ctx.unaryexpr());
            assert e != null;
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
            assert e != null;
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
    public SLExpression visitTransactionUpdated(JmlParser.TransactionUpdatedContext ctx) {
        String fieldName = "<transactionConditionallyUpdated>";
        return lookupIdentifier(fieldName, accept(ctx.expression()), null, ctx.start);
    }


    @Override
    public SLExpression visitPostfixexpr(JmlParser.PostfixexprContext ctx) {
        String oldFqName = fullyQualifiedName;
        fullyQualifiedName = "";
        SLExpression expr = accept(ctx.primaryexpr());

        for (JmlParser.PrimarysuffixContext c : ctx.primarysuffix()) {
            receiver = expr;
            expr = accept(c);
        }

        if (expr == null) {
            raiseError(format("Expression %s cannot be resolved.", fullyQualifiedName));
        }
        fullyQualifiedName = oldFqName;
        return expr;
    }

    @Override
    public Object visitIdent(JmlParser.IdentContext ctx) {
        appendToFullyQualifiedName(ctx.getText());
        return lookupIdentifier(ctx.getText(), null, null, ctx.start);
    }

    @Override
    public Object visitInv(JmlParser.InvContext ctx) {
        return translator.createInv(selfVar == null ? null : tb.var(selfVar), containerType);
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
        return getThisReceiver();
    }

    @NotNull
    private SLExpression getThisReceiver() {
        return new SLExpression(tb.var(selfVar), selfVar.getKeYJavaType());
    }

    private SLExpression lookupIdentifier(String lookupName,
                                          SLExpression receiver,
                                          SLParameters params,
                                          Token t) {
        exc.updatePosition(t);
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
        } catch (ClassCastException e) {

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

    //receiver value of attribute access, functions calls or array access
    private SLExpression receiver;
    private String fullyQualifiedName;

    @Override
    public SLExpression visitPrimarySuffixAccess(JmlParser.PrimarySuffixAccessContext ctx) {
        SLExpression receiver = this.receiver;
        String lookupName;
        boolean methodCall = ctx.LPAREN() != null;

        /*if (fullyQualifiedName.startsWith("\\dl_")) {
            return translator.dlKeyword(fullyQualifiedName, accept(ctx.expressionlist()));
        }*/

        SLParameters params = null;
        if (methodCall) {
            params = visitParameters(ctx.expressionlist());
            //lookupName = lookupName.substring(lookupName.lastIndexOf('.') + 1);

            /*SLExpression result = lookupIdentifier(lookupName, receiver, new SLParameters(params), ctx.LPAREN().getSymbol());
            if (result == null) {
                raiseError(String.format("Method %s(%s) not found!",
                        lookupName, createSignatureString(params)), ctx.LPAREN().getSymbol());
            }
            if (((IProgramMethod) result.getTerm().op()).getStateCount() > 1
                    && (atPres == null || atPres.get(getBaseHeap()) == null)) {
                raiseError("Two-state model method " + lookupName + " not allowed in this context!", ctx.LPAREN().getSymbol());
            }*/
        }

        if (ctx.IDENT() != null) {
            String id = ctx.IDENT().getText();
            if (receiver == null) {
                // Receiver was only a package/classname prefix
                lookupName = fullyQualifiedName + "." + id;
            } else {
                lookupName = id;
            }
            fullyQualifiedName = fullyQualifiedName + "." + id;
            try {
                return lookupIdentifier(lookupName, receiver, params, ctx.IDENT().getSymbol());
            } catch (Exception e) {
                return lookupIdentifier(fullyQualifiedName, null, null,
                        ctx.IDENT().getSymbol());
            }
        }
        if (ctx.TRANSIENT() != null) {
            assert !methodCall;
            return lookupIdentifier("<transient>", receiver, null, ctx.TRANSIENT().getSymbol());
        }
        if (ctx.THIS() != null) {
            assert !methodCall;
            SLExpression expr = new SLExpression(
                    services.getTypeConverter().findThisForSort(receiver.getType().getSort(),
                            tb.var(selfVar),
                            javaInfo.getKeYJavaType(selfVar.sort()),
                            true),
                    receiver.getType());
        }
        if (ctx.INV() != null) {
            assert !methodCall;
            return translator.createInv(receiver.getTerm(), receiver.getType());
        }
        if (ctx.MULT() != null) {
            assert !methodCall;
            return new SLExpression(tb.allFields(receiver.getTerm()),
                    javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
        }
        assert false;
        return null;
    }

    @Override
    public Object visitPrimarySuffixCall(JmlParser.PrimarySuffixCallContext ctx) {
        final SLExpression receiver = this.receiver;
        String lookupName = fullyQualifiedName;

        if (fullyQualifiedName.startsWith("\\dl_")) {
            return translator.dlKeyword(fullyQualifiedName, accept(ctx.expressionlist()));
        }
        SLParameters params = visitParameters(ctx.expressionlist());

        lookupName = lookupName.substring(lookupName.lastIndexOf('.') + 1);

        SLExpression result = lookupIdentifier(lookupName, receiver, params, ctx.LPAREN().getSymbol());
        if (result == null) {
            if (fullyQualifiedName.indexOf('.') < 0) {
                //resolve by prefixing an `this.`
                result = lookupIdentifier(lookupName, getThisReceiver(), params, ctx.LPAREN().getSymbol());
            }
            if (result == null) {
                raiseError(format("Method %s(%s) not found!",
                        lookupName, createSignatureString(params.getParameters())), ctx.LPAREN().getSymbol());
            }
        }
        if (((IProgramMethod) result.getTerm().op()).getStateCount() > 1
                && (atPres == null || atPres.get(getBaseHeap()) == null)) {
            raiseError("Two-state model method " + lookupName + " not allowed in this context!", ctx.LPAREN().getSymbol());
        }
        return result;
    }

    private SLParameters visitParameters(JmlParser.ExpressionlistContext ctx) {
        ImmutableList<SLExpression> params = accept(ctx);
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
        return new SLParameters(params);
    }

    @Override
    public Object visitPrimarySuffixArray(JmlParser.PrimarySuffixArrayContext ctx) {
        SLExpression curReceiver = receiver;
        SLExpression rangeFrom = accept(ctx.from);
        SLExpression rangeTo = accept(ctx.to);
        //TODO not handled by code ctx.MULT()
        return translator.arrayRef(curReceiver, fullyQualifiedName, rangeFrom, rangeTo);
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
        String text = ctx.getText();
        boolean isLong = text.endsWith("l") || text.endsWith("L");
        try {
            Literal literal = isLong ? new LongLiteral(text) : new IntLiteral(text);
            Term intLit = services.getTypeConverter().getIntegerLDT().translateLiteral(literal, services);
            PrimitiveType literalType = isLong ? PrimitiveType.JAVA_LONG : PrimitiveType.JAVA_INT;
            result = new SLExpression(intLit, javaInfo.getPrimitiveKeYJavaType(literalType));
        } catch (NumberFormatException e) {
            throw new RuntimeException(e.getMessage(), e);
        }
        return result;
    }


    @Override
    public Object visitPrimaryResult(JmlParser.PrimaryResultContext ctx) {
        if (resultVar == null) {
            raiseError("\\result used in wrong context");
        }
        appendToFullyQualifiedName("\\result");
        return new SLExpression(tb.var(resultVar), resultVar.getKeYJavaType());
    }

    private void appendToFullyQualifiedName(String suffix) {
        if (fullyQualifiedName.isEmpty())
            fullyQualifiedName = suffix;
        else
            fullyQualifiedName += "." + suffix;
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
        assert result != null;
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
        return new SLExpression(convertToPermission(((SLExpression) requireNonNull(accept(ctx.expression()))).getTerm()));
    }

    @Override
    public Object visitPrimaryNNE(JmlParser.PrimaryNNEContext ctx) {
        SLExpression result = accept(ctx.expression());
        assert result != null;
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
        return translator.commentary(ctx.INFORMAL_DESCRIPTION().getText(),
                selfVar, resultVar, paramVars, atPres == null ? null : atPres.get(getBaseHeap()));
    }

/*    @Override
    public Object visitPrimaryDLCall(JmlParser.PrimaryDLCallContext ctx) {
        String escape = ctx.JML_IDENT().getText();
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        return translator.dlKeyword(escape, list);
    }
*/

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
        //TODO atPres?
        final Term a = translator.notModified(atPres == null ? null : atPres.get(getBaseHeap()), t);
        assert a != null;
        return new SLExpression(a);
    }

    @Override
    public Object visitPrimaryNotAssigned(JmlParser.PrimaryNotAssignedContext ctx) {
        return translator.createSkolemExprBool(ctx.NOT_ASSIGNED().getText());
    }

    @Override
    public Object visitPrimaryFresh(JmlParser.PrimaryFreshContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.expressionlist());
        return translator.fresh(list, atPres);
    }

    @Override
    public SLExpression visitPrimaryReach(JmlParser.PrimaryReachContext ctx) {
        Term t = accept(ctx.storeref());
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = ctx.expression().size() == 3 ? accept(ctx.expression(2)) : null;
        assert e2 != null;
        assert e1 != null;
        return translator.reach(t, e1, e2, e3);
    }

    @Override
    public SLExpression visitPrimaryReachLocs(JmlParser.PrimaryReachLocsContext ctx) {
        Term t = accept(ctx.storeref());
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = ctx.expression().size() == 2 ? accept(ctx.expression(1)) : null;
        assert e1 != null;
        return translator.reachLocs(t, e1, e2, e3);
    }


    @Override
    public Object visitPrimaryDuration(JmlParser.PrimaryDurationContext ctx) {
        return translator.createSkolemExprLong(ctx.DURATION().getText());
    }

    @Override
    public Object visitPrimarySpace(JmlParser.PrimarySpaceContext ctx) {
        //TODO expression ignored
        return translator.createSkolemExprLong(ctx.SPACE().getText());
    }

    @Override
    public Object visitPrimaryWorksingSpace(JmlParser.PrimaryWorksingSpaceContext ctx) {
        //TODO expression ignored
        return translator.createSkolemExprLong(ctx.WORKINGSPACE().getText());
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
        assert result != null;
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
        assert typ != null;
        return new SLExpression(typ);
    }

    @Override
    public Object visitPrimaryLockset(JmlParser.PrimaryLocksetContext ctx) {
        return translator.createSkolemExprObject(ctx.LOCKSET().getText());
    }

    @Override
    public Object visitPrimaryIsInitialised(JmlParser.PrimaryIsInitialisedContext ctx) {
        KeYJavaType typ = accept(ctx.referencetype());
        assert typ != null;
        Term resTerm = tb.equals(tb.var(
                javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, typ)),
                tb.TRUE());
        return new SLExpression(resTerm);
    }

    @Override
    public SLExpression visitPrimaryInvFor(JmlParser.PrimaryInvForContext ctx) {
        SLExpression result = accept(ctx.expression());
        assert result != null;
        return translator.invFor(result);
    }

    @Override
    public SLExpression visitPrimaryStaticInv(JmlParser.PrimaryStaticInvContext ctx) {
        KeYJavaType typ = accept(ctx.referencetype());
        return translator.staticInfFor(typ);
    }

    @Override
    public Object visitPrimaryLblNeg(JmlParser.PrimaryLblNegContext ctx) {
        exc.addIgnoreWarning("\\lblneg", ctx.LBLNEG().getSymbol());
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryLblPos(JmlParser.PrimaryLblPosContext ctx) {
        exc.addIgnoreWarning("\\lblpos", ctx.LBLPOS().getSymbol());
        return accept(ctx.expression());
    }

    @Override
    public Object visitPrimaryIndex(JmlParser.PrimaryIndexContext ctx) {
        return translator.index();
    }

    @Override
    public Object visitPrimaryValues(JmlParser.PrimaryValuesContext ctx) {
        return translator.values(this.containerType);
    }

    @Override
    public Object visitPrimaryStringEq(JmlParser.PrimaryStringEqContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        Function strContent = services.getNamespaces().functions().lookup(CharListLDT.STRINGCONTENT_NAME);
        if (strContent == null) {
            raiseError("strings used in spec, but string content function not found");
        }
        assert e2 != null;
        assert e1 != null;
        return new SLExpression(tb.equals(tb.func(strContent, e1.getTerm()), tb.func(strContent, e2.getTerm())));
    }

    @Override
    public Object visitPrimaryEmptySet(JmlParser.PrimaryEmptySetContext ctx) {
        return translator.empty(javaInfo);
    }

    @Override
    public Object visitPrimaryignor9(JmlParser.Primaryignor9Context ctx) {
        Term t = accept(ctx.createLocset());
        assert t != null;
        return new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryUnion(JmlParser.PrimaryUnionContext ctx) {
        Term t = accept(ctx.storeRefUnion());
        return translator.createUnion(javaInfo, t);
    }

    @Override
    public Object visitPrimaryIntersect(JmlParser.PrimaryIntersectContext ctx) {
        Term t = accept(ctx.storeRefIntersect());
        return translator.createIntersect(t, javaInfo);
    }

    @Override
    public Object visitPrimarySetMinux(JmlParser.PrimarySetMinuxContext ctx) {
        Term t = accept(ctx.storeref(0));
        Term t2 = accept(ctx.storeref(1));
        assert t != null;
        return new SLExpression(tb.setMinus(t, t2),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryAllFields(JmlParser.PrimaryAllFieldsContext ctx) {
        SLExpression e1 = accept(ctx.expression());
        assert e1 != null;
        if (!e1.isTerm() || !e1.getTerm().sort().extendsTrans(services.getJavaInfo().objectSort())) {
            raiseError("Invalid argument to \\allFields: " + e1);
        }
        return new SLExpression(tb.allFields(e1.getTerm()),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryAllObj(JmlParser.PrimaryAllObjContext ctx) {
        Term t = accept(ctx.storeref());
        assert t != null;
        return new SLExpression(tb.allObjects(t.sub(1)),
                javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
    }

    @Override
    public Object visitPrimaryUnionInf(JmlParser.PrimaryUnionInfContext ctx) {
        System.err.println("!!! Deprecation Warnung: You used \\infinite_union in the functional syntax \\infinite_union(...)."
                + "\n\tThis is deprecated and won't be valid in future versions of KeY."
                + "\n\tPlease use \\infinite_union as a binder instead: (\\infinite_union var type; guard; store-ref-expr).");
        return createInfiniteUnion(ctx.boundvarmodifiers(), ctx.quantifiedvardecls(), ctx.predicate(), ctx.storeref());
    }

    @NotNull
    private Object createInfiniteUnion(JmlParser.BoundvarmodifiersContext boundvarmodifiers, JmlParser.QuantifiedvardeclsContext quantifiedvardecls, JmlParser.PredicateContext predicate, JmlParser.StorerefContext storeref) {
        Boolean nullable = accept(boundvarmodifiers);
        Pair<KeYJavaType, ImmutableList<LogicVariable>> declVars = accept(quantifiedvardecls);
        if (declVars != null) {
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
        }
        SLExpression t2 = accept(predicate);
        Term t = accept(storeref);
        if (declVars != null) resolverManager.popLocalVariablesNamespace();
        assert declVars != null;
        return translator.createUnionF(Boolean.TRUE.equals(nullable), declVars, t, t2 == null ? tb.tt() : t2.getTerm());
    }

    @Override
    public SLExpression visitPrimaryDisjoint(JmlParser.PrimaryDisjointContext ctx) {
        ImmutableList<Term> tlist = accept(ctx.storeRefList());
        assert tlist != null;
        return translator.createPairwiseDisjoint(tlist);
    }

    @Override
    public SLExpression visitPrimarySubset(JmlParser.PrimarySubsetContext ctx) {
        Term t = accept(ctx.storeref(0));
        Term t2 = accept(ctx.storeref(1));
        assert t != null;
        return new SLExpression(tb.subset(t, t2));
    }

    @Override
    public SLExpression visitPrimaryNewElemsfrehs(JmlParser.PrimaryNewElemsfrehsContext ctx) {
        Term t = accept(ctx.storeref());
        assert t != null;
        return new SLExpression(tb.subset(t,
                tb.union(convertToOld(t),
                        tb.freshLocs(atPres == null ? null : atPres.get(getBaseHeap())))));
    }

    @Override
    public SLExpression visitSequenceEmpty(JmlParser.SequenceEmptyContext ctx) {
        return new SLExpression(tb.seqEmpty());
    }

    @Override
    public SLExpression visitSequenceCreate(JmlParser.SequenceCreateContext ctx) {
        ImmutableList<SLExpression> list = accept(ctx.exprList());
        assert list != null;
        return translator.seqConst(list);
    }

    @Override
    public Object visitSequenceSub(JmlParser.SequenceSubContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = accept(ctx.expression(2));
        assert e3 != null;
        assert e2 != null;
        assert e1 != null;
        return new SLExpression(tb.seqSub(e1.getTerm(), e2.getTerm(), e3.getTerm()));
    }

    @Override
    public Object visitSequenceReverse(JmlParser.SequenceReverseContext ctx) {
        SLExpression e1 = accept(ctx.expression());
        assert e1 != null;
        return new SLExpression(tb.seqReverse(e1.getTerm()));
    }

    @Override
    public Object visitSequenceReplace(JmlParser.SequenceReplaceContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));
        SLExpression e3 = accept(ctx.expression(2));
        // short for "e1[0..e2-1]+e3+e1[e2+1..e1.length-1]"
        final Term minusOne = tb.zTerm("-1");
        assert e2 != null;
        assert e1 != null;
        final Term ante = tb.seqSub(e1.getTerm(), tb.zero(), tb.add(e2.getTerm(), minusOne));
        assert e3 != null;
        final Term insert = tb.seqSingleton(e3.getTerm());
        final Term post = tb.seqSub(e1.getTerm(), tb.add(e2.getTerm(), tb.one()), tb.add(tb.seqLen(e1.getTerm()), minusOne));
        final Term put = tb.seqConcat(ante, tb.seqConcat(insert, post));
        return new SLExpression(put);
    }

    @Override
    public Object visitSequenceFuncs(JmlParser.SequenceFuncsContext ctx) {
        SLExpression e1 = accept(ctx.expression(0));
        SLExpression e2 = accept(ctx.expression(1));

        assert e1 != null;
        assert e2 != null;

        final Term t2 = e2.getTerm();
        final Term t1 = e1.getTerm();
        switch (ctx.op.getType()) {
            case JmlLexer.SEQCONCAT:
                return translator.seqConcat(t1, t2);
            case JmlLexer.SEQGET:
                return translator.seqGet(t1, t2);
            case JmlLexer.INDEXOF:
                return translator.createIndexOf(t1, t2);
        }
        throw new IllegalStateException("Unknown operator: " + ctx.op);
    }

    @Override
    public Object visitInfinite_union_expr(JmlParser.Infinite_union_exprContext ctx) {
        return createInfiniteUnion(ctx.boundvarmodifiers(), ctx.quantifiedvardecls(), ctx.predicate(0), ctx.storeref());
    }

    @Override
    public SLExpression visitSpecquantifiedexpression(JmlParser.SpecquantifiedexpressionContext ctx) {
        boolean nullable = Boolean.TRUE == accept(ctx.boundvarmodifiers());
        Pair<KeYJavaType, ImmutableList<LogicVariable>> declVars = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        assert declVars != null;
        resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);

        Term guard = tb.tt();
        if (ctx.expression().size() == 2) {
            SLExpression a = accept(ctx.expression(0));
            assert a != null;
            guard = a.getTerm();
        }
        SLExpression expr =
                ctx.expression().size() == 2
                        ? accept(ctx.expression(1))
                        : accept(ctx.expression(0));

        resolverManager.popLocalVariablesNamespace();
        assert guard != null;
        guard = tb.convertToFormula(guard);
        assert expr != null;
        final Term body = expr.getTerm();
        switch (ctx.quantifier().start.getType()) {
            case JmlLexer.FORALL:
                return translator.forall(guard, body,
                        declVars.first, declVars.second,
                        nullable, expr.getType());
            case JmlLexer.EXISTS:
                return translator.exists(guard, body,
                        declVars.first, declVars.second,
                        nullable, expr.getType());
            case JmlLexer.MAX:
                return translator.quantifiedMax(guard, body,
                        declVars.first, nullable, declVars.second);
            case JmlLexer.MIN:
                return translator.quantifiedMin(guard, body,
                        declVars.first, nullable, declVars.second);
            case JmlLexer.NUM_OF:
                KeYJavaType kjtInt = services.getTypeConverter().getKeYJavaType(PrimitiveType.JAVA_BIGINT);
                return translator.quantifiedNumOf(guard, body,
                        declVars.first, nullable, declVars.second,
                        kjtInt);
            case JmlLexer.SUM:
                return translator.quantifiedSum(declVars.first, nullable,
                        declVars.second, guard, body,
                        expr.getType());
            case JmlLexer.PRODUCT:
                return translator.quantifiedProduct(declVars.first, nullable,
                        declVars.second, guard, body,
                        expr.getType());

        }
        throw new IllegalStateException();
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

        if (id != null)
            exc.addIgnoreWarning("\\old with label ", ctx.IDENT().getSymbol());

        assert result != null;
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

        assert result != null;
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
        @Nullable Pair<KeYJavaType, ImmutableList<LogicVariable>> decls = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        assert decls != null;
        resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        SLExpression a = accept(ctx.expression(0));
        SLExpression b = accept(ctx.expression(1));
        SLExpression t = accept(ctx.expression(2));
        assert t != null;
        SLExpression result = translator.bsum(a, b, t, decls.first, decls.second);
        resolverManager.popLocalVariablesNamespace();
        return result;
    }

    @Override
    public Object visitSeqdefterm(JmlParser.SeqdeftermContext ctx) {
        @Nullable Pair<KeYJavaType, ImmutableList<LogicVariable>> decls = accept(ctx.quantifiedvardecls());
        resolverManager.pushLocalVariablesNamespace();
        assert decls != null;
        resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
        SLExpression a = accept(ctx.expression(0));
        SLExpression b = accept(ctx.expression(1));
        SLExpression t = accept(ctx.expression(2));
        SLExpression result = translator.createSeqDef(a, b, t, decls.first, decls.second);
        resolverManager.popLocalVariablesNamespace();
        return result;
    }

    @Override
    public Pair<KeYJavaType, ImmutableList<LogicVariable>> visitQuantifiedvardecls(JmlParser.QuantifiedvardeclsContext ctx) {
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
        assert t != null;
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
        KeYJavaType varType;
        final Integer d = accept(ctx.dims());
        int dim = d == null ? 0 : d;
        String id = ctx.IDENT().toString();
        if (dim > 0) {
            StringBuilder fullName = new StringBuilder();
            if (t.getJavaType() instanceof ArrayType) {
                fullName.append(((ArrayType) t.getJavaType()).getAlternativeNameRepresentation());
            } else {
                fullName.append(t.getFullName());
            }
            for (int i = 0; i < dim; i++) {
                fullName.append("[]");
            }
            varType = javaInfo.getKeYJavaType(fullName.toString());
        } else {
            varType = t;
        }
        return new LogicVariable(new Name(id), varType.getSort());
    }
    //endregion

    //region contract
    private ImmutableSLList<String> mods;
    private JMLSpecFactory factory;
    private Object currentBehavior;
    private ContractClauses contractClauses = new ContractClauses();
    private final List<Term> abbreviations = new ArrayList<>(64);

    private PositionedString flipHeaps(String declString, PositionedString result) {
        return flipHeaps(declString, result, false);
    }

    /**
     * This method prepends a String to a given PositionedString and removes whitespaces from
     * heap brackets at the beginning of it. (Why is this necessary?)
     * <p>
     * Note: Static manipulation of Strings that are passed to KeYJMLParser is fragile when it
     * comes to error reporting. Original JML input should be left unmodified as much as possible
     * so that correct error location can be reported to the user. Functionality of this method
     * should be replaced by a more accurate implementation. (Kai Wallisch 07/2015)
     */
    private PositionedString flipHeaps(String declString, PositionedString result, boolean allowPreHeaps) {
        String t = result.text;
        String p = declString;

        List<Name> validHeapNames = new ArrayList<Name>();

        for (Name heapName : HeapLDT.VALID_HEAP_NAMES) {
            validHeapNames.add(heapName);
            if (allowPreHeaps) {
                validHeapNames.add(new Name(heapName.toString() + "AtPre"));
            }
        }
        for (Name heapName : validHeapNames) {
            t = t.trim();
            String l = "<" + heapName + ">";
            String lsp = "< " + heapName + " >";
            if (t.startsWith(l) || t.startsWith(lsp)) {
                p = l + p;
                t = t.substring(t.startsWith(lsp) ? lsp.length() : l.length());
                result = new PositionedString(t, result.fileName, result.pos);
            }
        }
        if (p.contains("<")) {
            /*
             * Using normal prepend without update of position in case p contains a heap
             * because in that case prependAndUpdatePosition() might produce a negative
             * column value. However, this alternative is also not ideal because it does
             * not update the position after prepending a string. A rewrite of this
             * method that does not rely on low-level string manipulation is recommended
             * to fix this issue.
             */
            result = result.prepend(p + " ");
        } else {
            result = result.prependAndUpdatePosition(p + " ");
        }
        return result;
    }


    @Override
    public Object visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
        if (ctx.COLON() != null || ctx.MEASURED_BY() != null) {//depends clause
            //depends clause
            SLExpression lhs = accept(ctx.lhs);
            Term rhs = accept(ctx.rhs);
            SLExpression mby = accept(ctx.mby);
            assert lhs != null;
            assert rhs != null;
            try {
                return translator.depends(lhs, rhs, mby);
            } catch (Exception e) {
                //weigl: seems strange maybe someone missed switched the values
                return translator.depends(new SLExpression(rhs), lhs.getTerm(), mby);
            }
        }
        final Term term = requireNonNull(accept(ctx.storeRefUnion()));
        Term t = translator.accessible(term);
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        for (LocationVariable heap : heaps) {
            contractClauses.add(ContractClauses.ACCESSIBLE, heap, t);
        }
        return new SLExpression(t);
    }

    @Override
    public SLExpression visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        Term t;
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        if (ctx.STRICTLY_NOTHING() != null) t = tb.strictlyNothing();
        else {
            final Term storeRef = accept(ctx.storeRefUnion());
            assert storeRef != null;
            t = translator.assignable(storeRef);
        }
        for (LocationVariable heap : heaps) {
            contractClauses.add(ContractClauses.ASSIGNABLE, heap, t);
        }
        return new SLExpression(t);
    }


    @Override
    public SLExpression visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        ImmutableList<KeYJavaType> typeList = ImmutableSLList.nil();
        for (JmlParser.ReferencetypeContext context : ctx.referencetype()) {
            typeList = typeList.append((KeYJavaType) accept(context));
        }
        Term t = translator.signalsOnly(typeList, this.excVar);
        contractClauses.signalsOnly = t;
        return new SLExpression(t);
    }


    @Override
    public Pair<Label, Term> visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        String label = ctx.lbl == null ? "" : ctx.lbl.getText(); //TODO weigl: right label if omitted
        SLExpression pred = accept(ctx.predornot());
        assert pred != null;
        @NotNull Pair<Label, Term> t = translator.createBreaks(pred.getTerm(), label);
        contractClauses.add(ContractClauses.BREAKS, t.first, t.second);
        return t;
    }

    @Override
    public Pair<Label, Term> visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        String label = ctx.lbl == null ? "" : ctx.lbl.getText(); //TODO weigl: right label if omitted
        SLExpression pred = accept(ctx.predornot());
        assert pred != null;
        @NotNull Pair<Label, Term> t = translator.createContinues(pred.getTerm(), label);
        contractClauses.add(ContractClauses.CONTINUES, t.first, t.second);
        return t;
    }

    @Override
    public SLExpression visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        @Nullable SLExpression pred = accept(ctx.predornot());
        assert pred != null;
        contractClauses.returns = translator.createReturns(pred.getTerm());
        return pred;
    }


    /*
    @Override
    public Triple<IObserverFunction, Term, Term> visitDepends_clause(JmlParser.Depends_clauseContext ctx) {
        SLExpression lhs = accept(ctx.expression(0));
        Term rhs = accept(ctx.storeRefUnion());
        SLExpression mby = accept(ctx.expression(1));
        assert lhs != null;
        Triple<IObserverFunction, Term, Term> a = translator.depends(lhs, rhs, mby);
        return a;
    }*/


    @Override
    public Object visitClasslevel_element0(JmlParser.Classlevel_element0Context ctx) {
        this.mods = ImmutableSLList.nil();
        /* there may be some modifiers after the declarations */
        this.mods = accept(ctx.modifiers());
        listOf(ctx.modifier2());
        return accept(ctx.classlevel_element());
    }

    @Override
    public ImmutableList<TextualJMLConstruct> visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
        mods = ImmutableSLList.nil();
        return null;
    }

    @Override
    public ImmutableList<String> visitModifiers(JmlParser.ModifiersContext ctx) {
        return listOf(ctx.modifier());
    }

    @Override
    public String visitModifier(JmlParser.ModifierContext ctx) {
        return ctx.getText();
    }


    @Override
    public SLExpression visitClass_invariant(JmlParser.Class_invariantContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public ClassAxiom visitClass_axiom(JmlParser.Class_axiomContext ctx) {
        // axiom statements may not be prefixed with any modifiers (see Sect. 8 of the JML reference manual)
        if (!mods.isEmpty())
            exc.raiseNotSupported("modifiers in axiom clause");
        return null;//factory.createJMLClassAxiom(kjt, mods, ctx.expression());
    }

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        for (String s : mods) {
            if (!(s.equals("public") || s.equals("private") || s.equals("protected")))
                exc.raiseNotSupported("modifier " + s + " in initially clause");
        }
        return null;// factory.createJMLInitiallyClause(kjt, mods, ctx.expression());
    }

    @Override
    public Object visitMethod_specification(JmlParser.Method_specificationContext ctx) {
        return listOf(ctx.spec_case());
    }

    //TODO init
    IProgramMethod pm = null;

    @Override
    public de.uka.ilkd.key.speclang.Contract visitSpec_case(JmlParser.Spec_caseContext ctx) {
        this.mods = accept(ctx.modifier());
        Behavior behavior = getBehavior(ctx.behavior, pm);
        String name = factory.generateName(pm, behavior, "name");
        contractClauses = new ContractClauses();
        accept(ctx.spec_body());
        //factory.createFunctionalOperationContracts();
        return null;
    }

    private Behavior getBehavior(Token behavior, IProgramMethod pm) {
        //TODO missing model behavior
        if (behavior == null) return Behavior.BEHAVIOR;
        return Behavior.valueOf(behavior.getText());
    }

    @Override
    public Object visitSpec_body(JmlParser.Spec_bodyContext ctx) {
        listOf(ctx.clause());
        listOf(ctx.spec_body());
        return null;//super.visitSpec_body(ctx);
    }


    enum ClauseSubType {NONE, FREE, REDUNDANT}

    private ClauseSubType subType(String type) {
        if (type.endsWith("_free")) return ClauseSubType.FREE;
        if (type.endsWith("_redundantly")) return ClauseSubType.FREE;
        return ClauseSubType.NONE;
    }

    private void insertSimpleClause(String type, LocationVariable heap, Term t,
                                    ContractClauses.Clauses<LocationVariable, Term> none,
                                    ContractClauses.Clauses<LocationVariable, Term> free,
                                    ContractClauses.Clauses<LocationVariable, Term> redundantly) {
        LocationVariable loc = null;
        switch (subType(type)) {
            case FREE:
                contractClauses.add(free, heap, t);
                break;
            case REDUNDANT:
                contractClauses.add(redundantly, heap, t);
                break;
            default:
                contractClauses.add(none, heap, t);
        }
    }

    @Override
    public Object visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
        String type = ctx.ENSURES().getText();
        SLExpression t = accept(ctx.predornot());
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        for (LocationVariable heap : heaps) {
            assert t != null;
            insertSimpleClause(type, heap, t.getTerm(),
                    ContractClauses.ENSURES,
                    ContractClauses.ENSURES_FREE,
                    ContractClauses.ENSURES);
        }
        return t;
    }


    @Override
    public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        String type = ctx.REQUIRES().getText();
        SLExpression t = accept(ctx.predornot());
        LocationVariable[] heaps = visitTargetHeap(ctx.targetHeap());
        for (LocationVariable heap : heaps) {
            assert t != null;
            insertSimpleClause(type, heap, t.getTerm(),
                    ContractClauses.REQUIRES,
                    ContractClauses.REQUIRES_FREE,
                    ContractClauses.REQUIRES);
        }
        return t;
    }

    @Override
    public Object visitMeasured_by_clause(JmlParser.Measured_by_clauseContext ctx) {
        final List<SLExpression> seq = ctx.predornot().stream().map(it -> (SLExpression) accept(it))
                .collect(Collectors.toList());
        Optional<SLExpression> t = seq.stream()
                .reduce((a, b) -> new SLExpression(tb.pair(a.getTerm(), b.getTerm())));
        Term result = t.orElse(seq.get(0)).getTerm();
        contractClauses.measuredBy = result;
        return new SLExpression(result);
    }


    @Override
    public Object visitCaptures_clause(JmlParser.Captures_clauseContext ctx) {
        return this.<SLExpression>accept(ctx.predornot());
    }

    @Override
    public Object visitDiverges_clause(JmlParser.Diverges_clauseContext ctx) {
        SLExpression t = accept(ctx.predornot());
        assert t != null;
        contractClauses.diverges = t.getTerm();
        return t;
    }

    @Override
    public Object visitWorking_space_clause(JmlParser.Working_space_clauseContext ctx) {
        //insertSimpleClause(type, t,
        //        contractClauses.requires, contractClauses.requiresFree, contractClauses.requires);
        return (this.<SLExpression>accept(ctx.predornot()));
    }

    @Override
    public Object visitDuration_clause(JmlParser.Duration_clauseContext ctx) {
        SLExpression t = accept(ctx.predornot());
        //insertSimpleClause(type, t,
        //        contractClauses., contractClauses.requiresFree, contractClauses.requires);
        return t;
    }

    @Override
    public Object visitWhen_clause(JmlParser.When_clauseContext ctx) {
        SLExpression t = accept(ctx.predornot());
        assert false;
        //insertSimpleClause(type, t,
        //        contractClauses., contractClauses.requiresFree, contractClauses.requires);
        return t;
    }


    @Override
    public Pair<IObserverFunction, Term> visitRepresents_clause(JmlParser.Represents_clauseContext ctx) {
        SLExpression lhs = accept(ctx.lhs);
        SLExpression rhs = accept(ctx.rhs);
        Term storeRef = accept(ctx.t);

        assert lhs != null;
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
        if (ctx.SUCH_THAT() != null)
            t = ((SLExpression) accept(ctx.predicate())).getTerm();
        else if (!representsClauseLhsIsLocSet) {
            assert rhs != null;
            if (!rhs.isTerm()) {
                raiseError("Represents clause with unexpected rhs: " + rhs);
            }
            Term rhsTerm = rhs.getTerm();
            if (rhsTerm.sort() == Sort.FORMULA) {
                rhsTerm = tb.ife(rhsTerm, tb.TRUE(), tb.FALSE());
            }
            t = tb.equals(lhs.getTerm(), rhsTerm);
        } else {
            t = rhs != null ? rhs.getTerm() : storeRef;
            assert t != null;
            t = tb.equals(lhs.getTerm(), t);
        }
        return translator.represents(lhs, t);
    }

    //region inf flow

    @Override
    public InfFlowSpec visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
        ImmutableList<Term> decl = ImmutableSLList.nil();
        ImmutableList<Term> erases = ImmutableSLList.nil();
        ImmutableList<Term> newObs = ImmutableSLList.nil();

        ImmutableList<Term> sep = accept(ctx.sep);

        decl = append(decl, ctx.decl);
        erases = append(erases, ctx.erase);
        newObs = append(newObs, ctx.newobj);
        assert sep != null;
        decl = sep.append(decl);
        erases = sep.append(erases);
        return new InfFlowSpec(decl, erases, newObs);
    }

    @Override
    public Object visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
        ImmutableList<Term> sep = accept(ctx.sep);
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        newObs = append(newObs, ctx.newobj);
        return new InfFlowSpec(sep, sep, newObs);
    }

    @Override
    public Object visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
        ImmutableList<Term> decl = ImmutableSLList.nil();
        ImmutableList<Term> erases = ImmutableSLList.nil();
        ImmutableList<Term> newObs = ImmutableSLList.nil();
        ImmutableList<Term> by = ImmutableSLList.nil();

        ImmutableList<Term> determined = accept(ctx.determined);

        if (ctx.byItself != null) {
            by = determined;
        } else {
            @Nullable ImmutableList<Term> t = accept(ctx.by);
            assert t != null;
            by = by.append(t);
        }

        decl = append(decl, ctx.decl);
        erases = append(erases, ctx.erases);
        newObs = append(newObs, ctx.newObs);

        assert determined != null;
        determined = determined.append(erases);
        by = by.append(decl);

        return new InfFlowSpec(by, determined, newObs);
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
        if (ctx.NOTHING() != null) return ImmutableSLList.nil();
        ImmutableList<SLExpression> seq = accept(ctx.expressionlist());
        assert seq != null;
        ImmutableList<Term> result = ImmutableList.fromList(
                seq.stream().map(SLExpression::getTerm).collect(Collectors.toList())
        );
        return translator.infflowspeclist(result);
    }
    //endregion

    @Override
    public Object visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
        LogicVariable eVar = null;
        KeYJavaType excType = accept(ctx.referencetype());
        String vName = accept(ctx.IDENT());
        if (vName != null) {
            assert excType != null;
            eVar = new LogicVariable(new Name(vName), excType.getSort());
            resolverManager.pushLocalVariablesNamespace();
            resolverManager.putIntoTopLocalVariablesNamespace(eVar, excType);
        }
        SLExpression result = accept(ctx.predornot());
        if (vName != null) {
            resolverManager.popLocalVariablesNamespace();
        }
        assert result != null;
        Term r = translator.signals(result.getTerm(), eVar, excVar, excType);
        contractClauses.signalsOnly = r;
        return new SLExpression(r);
    }

    @Override
    public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
        TODO();
        return super.visitName_clause(ctx);
    }

    @Override
    public Object visitOld_clause(JmlParser.Old_clauseContext ctx) {
        TODO();
        return super.visitOld_clause(ctx);
    }

    @Override
    public Object visitField_declaration(JmlParser.Field_declarationContext ctx) {
        TODO();
        return super.visitField_declaration(ctx);
    }

    @Override
    public SLExpression visitMethod_declaration(JmlParser.Method_declarationContext ctx) {
        //preStart(contextThread)
        // == (\dl_writePermissionObject(contextThread, \permission(this.number)));
        if (ctx.BODY() == null) return new SLExpression(tb.tt());

        String bodyString = ctx.BODY() == null ? ";" : ctx.BODY().getText();
        if (bodyString.charAt(0) != '{' || bodyString.charAt(bodyString.length() - 1) != '}')
            throw new IllegalStateException();
        bodyString = bodyString.substring(1, bodyString.length() - 1).trim();
        if (!bodyString.startsWith("return "))
            throw new IllegalStateException("return expected, instead: " + bodyString);
        int beginIndex = bodyString.indexOf(" ") + 1;
        int endIndex = bodyString.lastIndexOf(";");
        bodyString = bodyString.substring(beginIndex, endIndex);

        String paramsString;
        List<JmlParser.Param_declContext> paramDecls = ctx.param_list().param_decl();
        if (paramDecls.size() > 0)
            paramsString = "(" + paramDecls.stream().map(it -> it.p.getText()).collect(Collectors.joining(",")) + ")";
        else
            paramsString = "()"; //default no params

        String equality = ctx.IDENT() + paramsString + " == (" + bodyString + ")";
        ParserRuleContext equal = JmlFacade.parseExpr(equality);
        return accept(equal);
    }

    @Override
    public Object visitHistory_constraint(JmlParser.History_constraintContext ctx) {
        TODO();
        return super.visitHistory_constraint(ctx);
    }

    @Override
    public Object visitDatagroup_clause(JmlParser.Datagroup_clauseContext ctx) {
        TODO();
        return super.visitDatagroup_clause(ctx);
    }

    @Override
    public Object visitMonitors_for_clause(JmlParser.Monitors_for_clauseContext ctx) {
        TODO();
        return super.visitMonitors_for_clause(ctx);
    }

    @Override
    public Object visitReadable_if_clause(JmlParser.Readable_if_clauseContext ctx) {
        TODO();
        return super.visitReadable_if_clause(ctx);
    }

    @Override
    public Object visitWritable_if_clause(JmlParser.Writable_if_clauseContext ctx) {
        TODO();
        return super.visitWritable_if_clause(ctx);
    }

    @Override
    public Object visitIn_group_clause(JmlParser.In_group_clauseContext ctx) {
        TODO();
        return super.visitIn_group_clause(ctx);
    }

    @Override
    public Object visitMaps_into_clause(JmlParser.Maps_into_clauseContext ctx) {
        TODO();
        return super.visitMaps_into_clause(ctx);
    }

    @Override
    public Object visitNowarn_pragma(JmlParser.Nowarn_pragmaContext ctx) {
        TODO();
        return super.visitNowarn_pragma(ctx);
    }

    @Override
    public Object visitDebug_statement(JmlParser.Debug_statementContext ctx) {
        TODO();
        return super.visitDebug_statement(ctx);
    }

    @Override
    public Object visitSet_statement(JmlParser.Set_statementContext ctx) {
        TODO();
        return super.visitSet_statement(ctx);
    }

    @Override
    public Object visitMerge_point_statement(JmlParser.Merge_point_statementContext ctx) {
        TODO();
        return super.visitMerge_point_statement(ctx);
    }

    @Override
    public Object visitMergeparamsspec(JmlParser.MergeparamsspecContext ctx) {
        String latticeType = ctx.latticetype.getText();
        KeYJavaType phType = accept(ctx.typespec());
        String phName = ctx.phName.getText();
        LocationVariable placeholder = new LocationVariable(new ProgramElementName(phName), phType);
        resolverManager.putIntoTopLocalVariablesNamespace(placeholder);
        ImmutableList<SLExpression> expr = listOf(ctx.predicate());

        ImmutableList<Term> preds =
                ImmutableList.fromList(
                        expr.stream().map(SLExpression::getTerm)
                                .collect(Collectors.toList()));
        return new MergeParamsSpec(latticeType, placeholder, preds);
    }

    @Override
    public Object visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
        TODO();
        return super.visitLoop_specification(ctx);
    }

    @Override
    public Object visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public Object visitVariant_function(JmlParser.Variant_functionContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public Object visitInitialiser(JmlParser.InitialiserContext ctx) {
        TODO();
        return super.visitInitialiser(ctx);
    }

    @Override
    public Object visitBlock_specification(JmlParser.Block_specificationContext ctx) {
        TODO();
        return super.visitBlock_specification(ctx);
    }

    @Override
    public Object visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
        TODO();
        return super.visitBlock_loop_specification(ctx);
    }

    @Override
    public Object visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        if (ctx.UNREACHABLE() != null) return new SLExpression(tb.not(tb.tt()));
        return accept(ctx.expression());
    }

    @Override
    public Object visitAssume_statement(JmlParser.Assume_statementContext ctx) {
        return accept(ctx.expression());
    }

    @Override
    public LocationVariable[] visitTargetHeap(JmlParser.TargetHeapContext ctx) {
        if (ctx == null || ctx.SPECIAL_IDENT().size() == 0) return new LocationVariable[]{getBaseHeap()};
        LocationVariable[] heaps = new LocationVariable[ctx.SPECIAL_IDENT().size()];
        for (int i = 0; i < ctx.SPECIAL_IDENT().size(); i++) {
            String heapName = ctx.SPECIAL_IDENT(i).getText();
            switch (heapName) {
                case "<permission>":
                case "<permissions>":
                    heaps[i] = getPermissionHeap();
                    break;
                case "<savedHeap>":
                case "<saved>":
                    heaps[i] = getSavedHeap();
                    break;
                case "<heap>":
                    heaps[i] = getBaseHeap();
                    break;
                default:
                    heaps[i] = heapLDT.getHeapForName(new Name(heapName));
                    //throw new IllegalStateException("Unknown heap: " + heapName);
            }
        }
        return heaps;
    }
    //endregion

    //region exception helper
    private void raiseNotSupported(String feature) {
        throw new RuntimeException(feature + " not supported");
    }

    private void raiseNotSupported(TerminalNode elemtype) {
        throw new RuntimeException(elemtype.getText() + " not supported");
    }

    private void raiseError(String s, Token symbol) {
        raiseError(s);
    }

    private void raiseError(String msg) {
        throw new RuntimeException(msg);
    }

    List<PositionedString> getWarnings() {
        return exc.getWarnings();
    }
    //endregion
}