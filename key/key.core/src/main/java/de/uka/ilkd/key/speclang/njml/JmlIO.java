package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.mergerule.MergeParamsSpec;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Map;

/**
 * Stateful service for translating JML into KeY entities.
 * <p>
 * This facade stores a the parsing context of JML constructs, e.g., the return or self variable, the parameters.
 * You can set these values via the builder methods. The {@code translate*} methods translate
 * a given {@link ParserRuleContext} into a KeY-entity.
 * <p>
 * It also maintains the list of translation warnings, see {@link #getWarnings()}.
 * <p>
 * Internally, this is a type-safe wrapper around the visitor {@link Translator}.
 *
 * @author Alexander Weigl
 * @version 1 (7/1/20)
 * @see Translator
 */
public class JmlIO {
    private ImmutableList<PositionedString> warnings = ImmutableSLList.nil();

    private Services services;
    private KeYJavaType specInClass;
    private ProgramVariable selfVar;
    private ImmutableList<ProgramVariable> paramVars;
    private ProgramVariable resultVar;
    private ProgramVariable excVar;
    private Map<LocationVariable, Term> atPres;
    private Map<LocationVariable, Term> atBefores;

    /**
     * Generate an empty jml i/o instance. No very useful until a {@link #services(Services)} is provided.
     */
    public JmlIO() {
    }

    /**
     * Full constructor of this class. Prefer the use via builder methods.
     *
     * @param services    a service object used for constructing the terms
     * @param specInClass the class in which the expression and contracts should be evaluated
     * @param selfVar     the self variable considered for {@code this}-references
     * @param paramVars   a list of parameter variables
     * @param resultVar   the {@code \return}-variable
     * @param excVar      the variable to store exception
     * @param atPres      i do not know
     * @param atBefores   i do not know
     */
    public JmlIO(@NotNull Services services,
                 @Nullable KeYJavaType specInClass,
                 @Nullable ProgramVariable selfVar,
                 @Nullable ImmutableList<ProgramVariable> paramVars,
                 @Nullable ProgramVariable resultVar,
                 @Nullable ProgramVariable excVar,
                 @Nullable Map<LocationVariable, Term> atPres,
                 @Nullable Map<LocationVariable, Term> atBefores) {
        this.services = services;
        this.specInClass = specInClass;
        this.selfVar = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar = excVar;
        this.atBefores = atBefores;
        this.atPres = atPres;
    }

    //region translations
    /**
     * @param clause
     * @return
     */
    @SuppressWarnings("unchecked")
    public Pair<IObserverFunction, Term> translateRepresents(ParserRuleContext clause) {
        Object interpret = interpret(clause);
        return (Pair<IObserverFunction, Term>) interpret;
    }

    /**
     * @param clause
     * @return
     */
    public Pair<IObserverFunction, Term> translateRepresents(LabeledParserRuleContext clause) {
        //TODO no represents label
        Pair<IObserverFunction, Term> p = translateRepresents(clause.first);
        return new Pair<>(p.first, p.second);
    }

    /**
     * Checks whether the given {@code functionName} is a known JML function for KeY.
     *
     * @param functionName a string
     * @return true if the function is known
     * @see JmlTermFactory#jml2jdl
     */
    public static boolean isKnownFunction(String functionName) {
        return JmlTermFactory.jml2jdl.containsKey(functionName);
    }

    private Term attachTermLabel(Term term, OriginTermLabel.SpecType type) {
        return services.getTermBuilder().addLabel(term,
                new OriginTermLabel(new OriginTermLabel.Origin(type)));
    }


    /**
     * @param parserRuleContext
     * @param type
     * @return
     */
    public Pair<Label, Term> translateLabeledClause(
            ParserRuleContext parserRuleContext, OriginTermLabel.SpecType type) {
        Pair<Label, Term> t = (Pair<Label, Term>) interpret(parserRuleContext);
        return new Pair<>(t.first, attachTermLabel(t.second, type));
    }

    /**
     * @param parserRuleContext
     * @param type
     * @return
     */
    public Pair<Label, Term> translateLabeledClause(
            LabeledParserRuleContext parserRuleContext, OriginTermLabel.SpecType type) {
        Pair<Label, Term> t = (Pair<Label, Term>) interpret(parserRuleContext.first);//TODO weigl label
        return new Pair<>(t.first, attachTermLabel(t.second, type));
    }


    /**
     * @param ctx
     * @return
     */
    public MergeParamsSpec translateMergeParams(JmlParser.MergeparamsspecContext ctx) {
        return (MergeParamsSpec) interpret(ctx);
    }

    /**
     * @param concatenatedComment
     * @param fileName
     * @param pos
     * @return
     */
    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment, String fileName, Position pos) {
        return parseClassLevel(new PositionedString(concatenatedComment, fileName, pos));
    }

    /**
     * @param positionedString
     * @return
     */
    private ImmutableList<TextualJMLConstruct> parseClassLevel(PositionedString positionedString) {
        return JmlFacade.parseClasslevel(positionedString);
    }

    /**
     * @return
     */
    public ImmutableList<PositionedString> getWarnings() {
        return warnings;
    }

    /**
     * @param concatenatedComment
     * @param fileName
     * @param position
     * @return
     */
    public ImmutableList<TextualJMLConstruct> parseMethodlevel(String concatenatedComment, String fileName, Position position) {
        return JmlFacade.parseMethodlevel(new PositionedString(concatenatedComment, fileName, position));

    }

    /**
     * @param p
     * @return
     */
    public Term parseExpression(PositionedString p) {
        ParserRuleContext ctx = JmlFacade.parseExpr(p);
        SLExpression expr = (SLExpression) interpret(ctx);
        return expr.getTerm();
    }

    /**
     * @param ctx
     * @return
     */
    private Object interpret(ParserRuleContext ctx) {
        Translator visitor = new Translator(services, specInClass, selfVar, paramVars, resultVar,
                excVar, atPres, atBefores);
        Object obj = ctx.accept(visitor);
        ImmutableList<PositionedString> newWarnings = ImmutableList.fromList(visitor.getWarnings());
        warnings = warnings.prepend(newWarnings);
        return obj;
    }

    /**
     * @param expr
     * @return
     */
    public Term translateTerm(ParserRuleContext expr) {
        Object interpret = interpret(expr);
        if (interpret instanceof SLExpression) {
            return ((SLExpression) interpret).getTerm();
        } else {
            return (Term) interpret;
        }
    }

    /**
     * @param expr
     * @return
     */
    public Term translateTerm(LabeledParserRuleContext expr) {
        Term term = translateTerm(expr.first);
        if (expr.second != null)
            return services.getTermBuilder().addLabel(term, expr.second);
        else
            return term;
    }

    /**
     * @param expr
     * @param type
     * @return
     */
    public Term translateTerm(LabeledParserRuleContext expr, OriginTermLabel.SpecType type) {
        Term term = translateTerm(expr.first);
        OriginTermLabel origin = new OriginTermLabel(new OriginTermLabel.Origin(type));
        if (expr.second != null)
            return services.getTermBuilder().addLabel(term,
                    new ImmutableArray<>(origin, expr.second));
        else
            return services.getTermBuilder().addLabel(term, origin);
    }


    /**
     * @param expr
     * @param type
     * @return
     */
    public Term translateTerm(ParserRuleContext expr, OriginTermLabel.SpecType type) {
        Term t = translateTerm(expr);
        return attachTermLabel(t, type);
    }

    /**
     * @param input
     * @return
     */
    public Term parseExpression(String input) {
        ParserRuleContext ctx = JmlFacade.parseExpr(input);
        SLExpression expr = (SLExpression) interpret(ctx);
        return expr.getTerm();
    }

    /**
     * Translate the given context into an information flow specification.
     *
     * @param expr should be a {@link JmlParser.Separates_clauseContext} or {@link JmlParser.Determines_clauseContext},
     *             or {@link JmlParser.Loop_separates_clauseContext} or {@link JmlParser.Loop_determines_clauseContext}.
     * @return a information flow specification from the given context.
     * @throws ClassCastException if the {@code expr} is not suitable
     */
    public @NotNull InfFlowSpec translateInfFlow(@NotNull ParserRuleContext expr) {
        return (InfFlowSpec) this.interpret(expr);
    }

    /**
     * Translate the given context into an information flow specification.
     * Like {@link #translateInfFlow(ParserRuleContext)} but this method can also handles the given label.
     */
    public InfFlowSpec translateInfFlow(LabeledParserRuleContext expr) {
        return translateInfFlow(expr.first);//TODO weigl label?
    }

    /**
     * Translates the given context into a dependency contract, aka, accessible-clause or depends-clause.
     *
     * @param ctx should a {@link JmlParser.Accessible_clauseContext}
     * @return a dependency contract
     * @throws ClassCastException if the {@code ctx} is not suitable
     */
    public Triple<IObserverFunction, Term, Term> translateDependencyContract(ParserRuleContext ctx) {
        return (Triple<IObserverFunction, Term, Term>) interpret(ctx);
    }

    /**
     * @param ctx
     * @return
     */
    public Triple<IObserverFunction, Term, Term> translateDependencyContract(LabeledParserRuleContext ctx) {
        return translateDependencyContract(ctx.first);
    }
    //endregion

    /*
     * @return public Object parse(PositionedString expr) {
     * ParserRuleContext ctx = JmlFacade.parseTop(expr);
     * return ctx.accept(new Translator(services, specInClass, selfVar, paramVars, resultVar,
     * excVar, atPres, atBefores));
     * }
     */


    //region builder methods
    /**
     * @param selfVar
     * @return
     */
    public JmlIO selfVar(ProgramVariable selfVar) {
        this.selfVar = selfVar;
        return this;
    }

    /**
     * @param params
     * @return
     */
    public JmlIO parameters(ImmutableList<ProgramVariable> params) {
        this.paramVars = params;
        return this;
    }

    /**
     * @param excVar
     * @return
     */
    public JmlIO exceptionVariable(ProgramVariable excVar) {
        this.excVar = excVar;
        return this;
    }

    /**
     * @param atPres
     * @return
     */
    public JmlIO atPres(Map<LocationVariable, Term> atPres) {
        this.atPres = atPres;
        return this;
    }

    /**
     * @param resultVar
     * @return
     */
    public JmlIO resultVariable(ProgramVariable resultVar) {
        this.resultVar = resultVar;
        return this;
    }

    /**
     * @param services
     * @return
     */
    public JmlIO services(Services services) {
        this.services = services;
        return this;
    }

    /**
     * @param classType
     * @return
     */
    public JmlIO classType(KeYJavaType classType) {
        this.specInClass = classType;
        return this;
    }

    /**
     * @param atBefores
     * @return
     */
    public JmlIO atBefore(Map<LocationVariable, Term> atBefores) {
        this.atBefores = atBefores;
        return this;
    }


    /**
     * @return
     */
    public JmlIO clear() {
        resultVariable(null);
        atBefore(null);
        atPres(null);
        classType(null);
        selfVar(null);
        warnings = ImmutableSLList.nil();
        exceptionVariable(null);
        parameters(ImmutableSLList.nil());
        return this;
    }
    //endregion
}
