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

import de.uka.ilkd.key.ldt.Rational;
import org.key_project.util.ExtList;

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

/**
 *  JML \real literal.
 *  @author bruns
 */

public class RealLiteral extends Literal {

    /**
     * Textual representation of the value.
     */

    protected final Rational value;

    /**
     * Double literal.
     */

    public RealLiteral() {
        this(new Rational());
    }

    public RealLiteral (int value){
        this(new Rational(value));
    }
    public RealLiteral(double value) {
        this(new Rational(value));
    }

    public RealLiteral(java.math.BigDecimal value) {
        this(new Rational(value));
    }

    public RealLiteral(ExtList children, String value) {
        super(children);
        this.value = new Rational(value);
    }

    public RealLiteral(ExtList children){
        super(children);
        this.value = new Rational();
    }

    private RealLiteral(Rational value) {
        this.value = value;
    }

    /** tests if equals
     */
    public boolean equalsModRenaming(	SourceElement o,
										NameAbstractionTable nat) {
		if (!(o instanceof RealLiteral)) {
		    return false;
		}
		return ((RealLiteral)o).getValue().equals(getValue());
    }

    @Override
    public int computeHashCode() {
        return 17 * super.computeHashCode() + getValue().hashCode();
    }

    /**
 *      Get value.
 *      @return the string.
     */

    public String getValue() {
        return value.toString();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
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
