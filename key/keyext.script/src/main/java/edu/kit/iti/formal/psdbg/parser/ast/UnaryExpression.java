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
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.NonNull;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 1 (30.04.17)
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class UnaryExpression extends Expression<ParserRuleContext> {
    @NonNull
    private Operator operator;
    @NonNull
    private Expression expression;

    /**
     * {@inheritDoc
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc
     */
    @Override
    public UnaryExpression copy() {
        UnaryExpression u = new UnaryExpression(operator, expression.copy());
        u.setRuleContext(this.getRuleContext());
        return u;
    }

    /**
     * {@inheritDoc
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        if (operator.arity() != 1)
            throw new NotWelldefinedException("Arity mismatch!", this);
        checkType(operator.type()[0], expression, signature);
        return operator.returnType();
    }

    @Override
    public boolean hasMatchExpression() {
        return expression.hasMatchExpression();
    }

    /**
     * {@inheritDoc
     */
    @Override
    public int getPrecedence() {
        return Operator.NOT.precedence();//a placeholder, because MINUS is used as binary operator,too
    }


    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getExpression()};
    }
}
