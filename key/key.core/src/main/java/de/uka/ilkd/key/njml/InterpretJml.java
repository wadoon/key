package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import org.key_project.util.collection.ImmutableList;

import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (5/14/20)
 */
public class InterpretJml {
    /*
    private Translator exprVisitor;

    public InterpretJml(Services services, KeYJavaType specInClass,
                        ProgramVariable self, ImmutableList<ProgramVariable> paramVars,
                        ProgramVariable result, ProgramVariable exc, Map<LocationVariable, Term> atPres,
                        Map<LocationVariable, Term> atBefores) {
        exprVisitor = new Translator(
                services, specInClass, self, paramVars,
                result, exc, atPres, atBefores);

    }

    public Term parseExpr(String expr) {
        return (Term) JmlFacade.parseExpr(expr).accept(exprVisitor);
    }*/
}
