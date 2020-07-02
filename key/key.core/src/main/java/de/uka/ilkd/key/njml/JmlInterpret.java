package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import org.key_project.util.collection.ImmutableList;

import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (7/1/20)
 */
public class JmlInterpret {
    public JmlInterpret(PositionedString expr, Services services, KeYJavaType specInClass, ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar, ProgramVariable excVar, Map<LocationVariable, Term> atPres) {
        System.out.println("JmlInterpret.JmlInterpret");
    }

    public JmlInterpret(PositionedString expr, Services services, KeYJavaType specInClass, ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar, ProgramVariable excVar, Map<LocationVariable, Term> atPres, Map<LocationVariable, Term> atBefores) {
        System.out.println("JmlInterpret.JmlInterpret");
    }
}
