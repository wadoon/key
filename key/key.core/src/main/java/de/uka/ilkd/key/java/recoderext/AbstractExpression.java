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

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.StatementContainer;
import recoder.java.expression.Assignment;

/**
 * An {@link AbstractExpression} "\abstract_expression e;" represents an
 * arbitrary Java expression and is handled as such. In particular, it may throw
 * an exception, and access all accessible variables / fields.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractExpression extends JavaNonTerminalProgramElement
        implements Expression, AbstractProgramElement {
    private static final long serialVersionUID = 1L;
    // NOTE (DS, 2019-10-31): Don't know what I'm doing here...
    private ExpressionContainer expressionContainer = null;

    private StatementContainer astParent;
    private String id;

    public AbstractExpression(String id) {
        this.id = id;
    }

    public AbstractExpression() {
        this(null);
    }

    @Override
    public NonTerminalProgramElement getASTParent() {
        return astParent;
    }

    public String getId() {
        return id;
    }

    public void setId(String id) {
        this.id = id;
    }

    public String getName() {
        return "_abstract " + id;
    }

    @Override
    public void accept(SourceVisitor visitor) {
        // TODO: Check if we have to do anything
    }

    @Override
    public Assignment deepClone() {
        throw new RuntimeException("Unimplemented");
    }

    @Override
    public ExpressionContainer getExpressionContainer() {
        return expressionContainer;
    }

    @Override
    public void setExpressionContainer(ExpressionContainer expressionContainer) {
        this.expressionContainer = expressionContainer;        
    }

    @Override
    public ProgramElement getChildAt(int arg0) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public int getChildCount() {
        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public int getChildPositionCode(ProgramElement pe) {
        return 0;
    }

    @Override
    public boolean replaceChild(ProgramElement pe1, ProgramElement pe2) {
        return false;
    }
}