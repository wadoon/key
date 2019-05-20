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

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;


public class Assume extends JavaStatement implements ExpressionContainer {

    private Expression condition;

    public Assume(Expression condition, PositionInfo pos) {
        super(pos);
        assert condition != null;
        this.condition = condition;
    }
   

    public Expression getExpressionAt(int index) {
        if (index == 0) { return condition; }
        throw new IndexOutOfBoundsException();
    }

    public int getExpressionCount() {        
        return 1;
    }

    public ProgramElement getChildAt(int index) {        
        return getExpressionAt(index);
    }

    public int getChildCount() {        
        return getExpressionCount();
    }

    public void visit(Visitor v) {
        v.performActionOnAssume(this);
    }

    public Expression getCondition() {
        return condition;
    }
    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printAssume(this);
    }
}