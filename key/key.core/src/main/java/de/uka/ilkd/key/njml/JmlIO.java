package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
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
        System.out.println("JmlIO.JmlIO");
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

    public ImmutableList<TextualJMLConstruct> parseClassLevel(String concatenatedComment, String fileName, Position pos) {
        return parseClassLevel(new PositionedString(concatenatedComment, fileName, pos));
    }

    private ImmutableList<TextualJMLConstruct> parseClassLevel(PositionedString positionedString) {
        System.out.println(positionedString.text);
        JmlParser p = JmlFacade.createParser(JmlFacade.createLexer(positionedString));
        //JmlParser.TopContext ctx = p.top();
        return ImmutableSLList.nil();
    }

    public ImmutableSet<? extends PositionedString> getWarnings() {
        return warnings;
    }

    public void setWarnings(ImmutableSet<? extends PositionedString> warnings) {
        this.warnings = warnings;
    }

    public ImmutableList<TextualJMLConstruct> parseMethodlevel(String concatenatedComment, String fileName, Position position) {
        return ImmutableSLList.nil();
    }

    public Term parseExpression(PositionedString p) {
        ParserRuleContext ctx = JmlFacade.parseExpr(p);
        SLExpression expr = (SLExpression) ctx.accept(new Translator(services, specInClass, selfVar, paramVars, resultVar,
                excVar, atPres, atBefores));
        return expr.getTerm();
    }

    public Object parse(PositionedString expr) {
        ParserRuleContext ctx = JmlFacade.parseTop(expr);
        return ctx.accept(new Translator(services, specInClass, selfVar, paramVars, resultVar,
                excVar, atPres, atBefores));
    }
}
