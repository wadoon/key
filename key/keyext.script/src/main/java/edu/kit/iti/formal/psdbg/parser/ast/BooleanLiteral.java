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
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import org.antlr.v4.runtime.Token;

/**
 * Represents a boolean literal (ie. {@link #FALSE} or {@link #TRUE}).
 * <p>
 * Instantiating can be useful for setting a custom {@link #setToken(Token)} and position.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
@Data
@EqualsAndHashCode(callSuper = false)
@Getter
public class BooleanLiteral extends Literal {
    public static final BooleanLiteral FALSE = new BooleanLiteral(false);
    public static final BooleanLiteral TRUE = new BooleanLiteral(true);

    private final boolean value;

    public BooleanLiteral(boolean value, Token token) {
        this.value = value;
        setToken(token);
    }

    BooleanLiteral(boolean b) {
        this(b, null);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BooleanLiteral copy() {
        return new BooleanLiteral(value, getToken());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SimpleType getType(Signature signature) throws NotWelldefinedException {
        return SimpleType.BOOL;
    }
}
