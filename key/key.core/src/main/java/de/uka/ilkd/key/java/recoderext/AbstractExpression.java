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
import recoder.java.reference.TypeReference;

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
    private TypeReference typeReference;

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

    /**
     * @return the typeReference
     */
    public TypeReference getTypeReference() {
        return typeReference;
    }

    /**
     * @param typeReference the typeReference to set
     */
    public void setTypeReference(TypeReference typeReference) {
        this.typeReference = typeReference;
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
    public ProgramElement getChildAt(int i) {
        if (i == 0) {
            return typeReference;
        } else {
            throw new IndexOutOfBoundsException();
        }
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public int getChildPositionCode(ProgramElement pe) {
        return typeReference.equals(pe) ? 0 : -1;
    }

    @Override
    public boolean replaceChild(ProgramElement pe1, ProgramElement pe2) {
        if (typeReference.equals(pe1)) {
            assert pe2 instanceof TypeReference;
            typeReference = (TypeReference) pe2;
            return true;
        }

        return false;
    }
}