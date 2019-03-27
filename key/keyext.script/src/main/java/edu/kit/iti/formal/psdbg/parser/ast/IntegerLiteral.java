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
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.Data;
import org.antlr.v4.runtime.Token;

import java.math.BigInteger;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
@Data
public class IntegerLiteral extends Literal {
    private final BigInteger value;

    public IntegerLiteral() {
        this(BigInteger.ZERO);
    }

    public IntegerLiteral(BigInteger value) {
        this.value = value;
    }

    public IntegerLiteral(Token digits) {
        setToken(digits);
        value = new BigInteger(digits.getText());
    }

    /**
     * {@inheritDoc}
     */
    @Override public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override public IntegerLiteral copy() {
        IntegerLiteral il = new IntegerLiteral(value);
        il.setToken(getToken());
        return il;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        return SimpleType.INT;
    }


    public BigInteger getValue() {
        return value;
    }
}
