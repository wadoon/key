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
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.types.TermType;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.Data;

/**
 * A match expression contains an argument and a uses clause.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
@Data
public class MatchExpression extends Expression<ScriptLanguageParser.MatchPatternContext> {
    //private Signature signature = new Signature();
    private Expression pattern;
    private boolean isDerivable = false;
    @Deprecated
    private Expression derivableTerm;

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{pattern};
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchExpression copy() {
        MatchExpression me = new MatchExpression();
        //if (signature != null)
        //    me.signature = signature.copy();
        me.pattern = pattern.copy();
        me.setRuleContext(this.ruleContext);
        return me;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        Type patternType = pattern.getType(signature);
        if (!(patternType instanceof TermType || patternType == SimpleType.STRING)) {
            throw new NotWelldefinedException("Missing parameter", this);
        }
        return SimpleType.BOOL;
    }

    @Override
    public boolean hasMatchExpression() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getPrecedence() {
        return Operator.MATCH.precedence();
    }
}
