// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.expression.literal.RealLiteral;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;

/**
 * Complete this class if you want to add support for the JML \real type.
 *
 * At the moment this class contains only stubs.
 * @author bruns, mulbrich
 */
public final class RealLDT extends LDT {

    public static final Name NAME = new Name("real");
    
    public static final String R_NAME = "R";
    private final Function theRealSymbol;

    public RealLDT(TermServices services) {
        super(NAME, services);
        this.theRealSymbol = services.getNamespaces().functions().lookup(R_NAME);
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
                                 Term[] subs,
                                 Services services,
                                 ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
                                 Term left,
                                 Term right,
                                 Services services,
                                 ExecutionContext ec) {
        return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
                                 Term sub,
                                 TermServices services,
                                 ExecutionContext ec) {
        return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof RealLiteral : "Must be a \\real literal";
        RealLiteral rlit = (RealLiteral) lit;
        return services.getTermBuilder().and();
    }


    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
                                   Services services,
                                   ExecutionContext ec) {
        assert false;
        return null;
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }


    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        return null;
    }


    @Override
    public final Type getType(Term t) {
        if(t.sort() == targetSort()) {
            return PrimitiveType.JAVA_REAL;
        } else {
            return null;
        }
    }

    public Function getRealSymbol() {
        return theRealSymbol;
    }
}