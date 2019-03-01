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
import lombok.EqualsAndHashCode;
import lombok.NonNull;
import lombok.RequiredArgsConstructor;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
@Data
@RequiredArgsConstructor
@EqualsAndHashCode(callSuper = false)
public class Variable extends Literal implements Comparable<Variable> {
    public static final String MAGIC_PREFIX = "#";

    @NonNull private String identifier;

    public Variable(Token variable) {
        this(variable.getText());
        setToken(variable);
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    @Override
    public Variable copy() {
        Variable v = new Variable(identifier);
        v.setToken(getToken());
        return v;
    }

    /**
     * Expression getType
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        if (signature.containsKey(this))
            return signature.get(this);
        throw new NotWelldefinedException(toString() + "not defined in signature.", this);
    }

    @Override
    public int compareTo(Variable o) {
        return identifier.compareTo(o.getIdentifier());
    }
}
