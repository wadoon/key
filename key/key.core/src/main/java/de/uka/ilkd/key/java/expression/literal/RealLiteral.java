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

package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.Name;

import java.io.IOException;
import java.math.BigDecimal;

/**
 *  JML \real literal. ... An extension to the Java ASTs
 *
 *  @author bruns, Rosa Abbasi, Mattias Ulbrich
 */

public class RealLiteral extends Literal {

    public static final String REAL_SUFFIX = "r";

    /**
     * Textual representation of the literal.
     */
    private final String string;

    /**
     * Value representation of the literal.
     */
    private final BigDecimal value;

    public RealLiteral() {
        this(0);
    }

    public RealLiteral (int value){
        this(value + REAL_SUFFIX);
    }

    public RealLiteral(double value) {
        this(value + REAL_SUFFIX);
    }

    public RealLiteral(java.math.BigDecimal value) {
        this(value + REAL_SUFFIX);
    }

    public RealLiteral(String string) {
        if (!string.toLowerCase().endsWith("r")) {
            throw new NumberFormatException(string);
        }

        try {
            this.value = new BigDecimal(string.substring(0, string.length()-1)).stripTrailingZeros();
        } catch (NumberFormatException e) {
            throw (NumberFormatException)
                    new NumberFormatException("BigDecimal has a limited range " +
                            "for the exponent. Perhaps the implementation needs " +
                            "to be adapted.").initCause(e);
        }
        this.string = string;
    }

    /**
     * tests if this is semantically equal to another element
     */
    public boolean equalsModRenaming(SourceElement o,
                                     NameAbstractionTable nat) {
        if (!(o instanceof RealLiteral)) {
            return false;
        }
        return ((RealLiteral)o).getValue().equals(getValue());
    }

    @Override
    public int computeHashCode() {
        return 17 * super.computeHashCode() + getString().hashCode();
    }

    public BigDecimal getValue() {
        return value;
    }

    public String getString() {
        return string;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnRealLiteral(this);
    }

    @Override
    protected void prettyPrintMain(PrettyPrinter w) throws IOException {
        w.printRealLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_REAL);
    }

    @Override
    public Name getLDTName() {
        return RealLDT.NAME;
    }
}
