package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
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
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (7/1/20)
 */
public class JmlIO {
    private ImmutableSet<? extends PositionedString> warnings = DefaultImmutableSet.nil();

    public JmlIO(Services services, KeYJavaType containerType,
                 ProgramVariable self, ImmutableList<ProgramVariable> o, ProgramVariable o1, ProgramVariable o2, Map<LocationVariable, Term> o3) {
        this(services, containerType, self, o, o1, o2, o3, new HashMap<>());
    }

    public JmlIO() {
    }

    private Services services;
    private KeYJavaType specInClass;
    private ProgramVariable selfVar;
    private ImmutableList<ProgramVariable> paramVars;
    private ProgramVariable resultVar;
    private ProgramVariable excVar;
    private Map<LocationVariable, Term> atPres;
    private Map<LocationVariable, Term> atBefores;

    public JmlIO(Services services, KeYJavaType specInClass, ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar, ProgramVariable excVar, Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores) {
        this.services = services;
        this.specInClass = specInClass;
        this.selfVar = selfVar;
        this.paramVars = paramVars;
        this.resultVar = resultVar;
        this.excVar = excVar;
        this.atBefores = atBefores;
        this.atPres = atPres;
    }

    public Pair<IObserverFunction, Term> translateRepresents(ParserRuleContext clause) {
        Object interpret = interpret(clause);
        return (Pair<IObserverFunction, Term>) interpret;
    }

    public static boolean isKnownFunction(String functionName) {
        return JmlTermFactory.jml2jdl.containsKey(functionName);
    }

    public static Term translateTerm(ParserRuleContext expr,
                                     KeYJavaType containerType,
                                     ProgramVariable self,
                                     ImmutableList<ProgramVariable> o, ProgramVariable o1, ProgramVariable o2, Map<LocationVariable, Term> o3, Services services) {
        JmlIO io = new JmlIO(services, containerType, self, o, o1, o2, o3);
        return (Term) io.interpret(expr);
    }

    public static Term translateTerm(ParserRuleContext expr, KeYJavaType containerType, ProgramVariable selfVar, ImmutableList<ProgramVariable> allVars,
                                     ProgramVariable o, ProgramVariable o1, Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atPres1, OriginTermLabel.SpecType type, Services services) {
        JmlIO io = new JmlIO(services, containerType, selfVar, allVars, o, o1, atPres, atPres1);
        SLExpression e = (SLExpression) io.interpret(expr);
        //TODO weigl set label
        return e.getTerm();
    }


    public static Pair<Label, Term> translateLabeledClause(
            ParserRuleContext parserRuleContext, KeYJavaType containerType,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, ProgramVariable excVar,
            Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores,
            OriginTermLabel.SpecType type, Services services) {
        //FIXME attach type to the generated terms
        JmlIO io = new JmlIO(services, containerType, selfVar, paramVars, resultVar, excVar, atPres, atBefores);
        Pair<Label, Term> t = (Pair<Label, Term>) io.interpret(parserRuleContext);
        return t;
        /*String label;
        if (parserRuleContext instanceof JmlParser.Continues_clauseContext) {
            label = ((JmlParser.Continues_clauseContext) parserRuleContext).IDENT().getText();
        } else if (parserRuleContext instanceof JmlParser.Breaks_clauseContext) {
            label = ((JmlParser.Breaks_clauseContext) parserRuleContext).IDENT().getText();
        } else {
            throw new IllegalArgumentException();
        }
        return new Pair<>(new ProgramElementName(label), t);*/
    }

    public MergeParamsSpec translateMergeParams(JmlParser.MergeparamsspecContext ctx) {
        return (MergeParamsSpec) interpret(ctx);
    }

    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment, String fileName, Position pos) {
        return parseClassLevel(new PositionedString(concatenatedComment, fileName, pos));
    }

    private ImmutableList<TextualJMLConstruct> parseClassLevel(PositionedString positionedString) {
        return JmlFacade.parseClasslevel(positionedString);
    }

    public ImmutableSet<? extends PositionedString> getWarnings() {
        return warnings;
    }

    public void setWarnings(ImmutableSet<? extends PositionedString> warnings) {
        this.warnings = warnings;
    }

    public ImmutableList<TextualJMLConstruct> parseMethodlevel(String concatenatedComment, String fileName, Position position) {
        return JmlFacade.parseMethodlevel(new PositionedString(concatenatedComment, fileName, position));

    }

    public Term parseExpression(PositionedString p) {
        ParserRuleContext ctx = JmlFacade.parseExpr(p);
        SLExpression expr = (SLExpression) interpret(ctx);
        return expr.getTerm();
    }

    private Object interpret(ParserRuleContext ctx) {
        return ctx.accept(new Translator(services, specInClass, selfVar, paramVars, resultVar,
                excVar, atPres, atBefores));
    }

    public Term translateTerm(ParserRuleContext expr) {
        Object interpret = interpret(expr);
        return ((SLExpression) interpret).getTerm();
    }

    public Term parseExpression(String input) {
        ParserRuleContext ctx = JmlFacade.parseExpr(input);
        SLExpression expr = (SLExpression) interpret(ctx);
        return expr.getTerm();
    }

    public Object parse(PositionedString expr) {
        ParserRuleContext ctx = JmlFacade.parseTop(expr);
        return ctx.accept(new Translator(services, specInClass, selfVar, paramVars, resultVar,
                excVar, atPres, atBefores));
    }


    public JmlIO selfVar(ProgramVariable selfVar) {
        this.selfVar = selfVar;
        return this;
    }

    public JmlIO parameters(ImmutableList<ProgramVariable> params) {
        this.paramVars = params;
        return this;
    }

    public JmlIO exceptionVariable(ProgramVariable excVar) {
        this.excVar = excVar;
        return this;
    }

    public JmlIO atPres(Map<LocationVariable, Term> atPres) {
        this.atPres = atPres;
        return this;
    }

    public JmlIO resultVariable(ProgramVariable resultVar) {
        this.resultVar = resultVar;
        return this;
    }

    public JmlIO services(Services services) {
        this.services = services;
        return this;
    }

    public JmlIO classType(KeYJavaType classType) {
        this.specInClass = classType;
        return this;
    }

    public InfFlowSpec translateInfFlow(ParserRuleContext expr) {
        return (InfFlowSpec) this.interpret(expr);
    }

    public Triple<IObserverFunction, Term, Term> translateDependencyContract(ParserRuleContext ctx) {
        return (Triple<IObserverFunction, Term, Term>) interpret(ctx);
    }
}