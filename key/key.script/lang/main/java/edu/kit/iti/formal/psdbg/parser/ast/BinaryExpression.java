package edu.kit.iti.formal.psdbg.parser.ast;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.Data;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
@Data
public class BinaryExpression extends Expression<ParserRuleContext> {
    private Expression left, right;
    private Operator operator;

    public BinaryExpression() {
    }

    public BinaryExpression(Expression left, Operator operator, Expression right) {
        this.left = left;
        this.operator = operator;
        this.right = right;
    }

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getLeft(), getRight()};
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BinaryExpression copy() {
        BinaryExpression be = new BinaryExpression(left.copy(), operator, right.copy());
        be.setRuleContext(this.ruleContext);
        return be;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        if (operator.arity() != 2)
            throw new NotWelldefinedException("Arity mismatch", this);

        checkType(operator.type()[0], left, signature);
        checkType(operator.type()[1], right, signature);

        return operator.returnType();
    }

    @Override
    public boolean hasMatchExpression() {
        return left.hasMatchExpression() || right.hasMatchExpression();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getPrecedence() {
        return operator.precedence();
    }
}
