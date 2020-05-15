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

package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Private;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableList;

/**
 * A factory for creating class invariants and operation contracts from textual JML specifications.
 * This is the public interface to the jml.translation package.
 */
public class JMLSpecFactory2 extends JMLSpecFactory {
    public JMLSpecFactory2(Services services, ExpressionTranslator et) {
        super(services);
    }

    public ClassInvariantImpl createJMLClassInvariant(
            KeYJavaType kjt, ImmutableList<String> mods, String name, ParserRuleContext expr) {
        final boolean isStatic = (mods.contains("static") || // modifier
                // "static"
                // in an interface "static" is the default (see Sect. 2.5 of the
                // reference manual)
                (services.getJavaInfo().isInterface(kjt) && !mods.contains("instance")));

        // create variable for self
        ProgramVariable selfVar = isStatic ? null : tb.selfVar(kjt, false);

        // translateToTerm expression
        //Term inv = tb.convertToFormula(JMLTranslator.translate(textualInv.getInv(), kjt, selfVar,
        //        null, null, null, null, null, Term.class, services));

        Term inv = parseExpression(expr);

        // create invariant
        name = getDefaultInvName(null, kjt);
        String display = getDefaultInvName(name, kjt);
        return new ClassInvariantImpl(name, display, kjt, getVisibility(mods), inv, selfVar);
    }

    private Term parseExpression(ParserRuleContext expr) {
        ExpressionTranslator expressionTranslator
                = null;// new ExpressionTranslator(services, kjt, self, paramVars, result, exc, atPres, atBefores);
        return (Term) expr.accept(expressionTranslator);
    }

    protected VisibilityModifier getVisibility(ImmutableList<String> mods) {
        for (String mod : mods) {
            if (mod.equals("private")) {
                return new Private();
            } else if (mod.equals("protected")) {
                return new Protected();
            } else if (mod.equals("public")) {
                return new Public();
            }
        }
        return null;
    }
}
