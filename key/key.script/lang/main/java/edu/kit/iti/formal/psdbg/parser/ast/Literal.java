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


import lombok.Getter;
import lombok.Setter;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public abstract class Literal extends Expression<ParserRuleContext> {
    @Getter
    @Setter
    private Token token;

    public void setToken(Token token) {
        this.token = token;
        if (token != null) {
            startPosition = Position.start(token);
            endPosition = Position.end(token);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getPrecedence() {
        return 0;
    }

    /**
     * {@link Literal}s do not have any {@link ParserRuleContext}
     *
     * @return always {@link Optional#empty()}
     */
    @Override
    public ParserRuleContext getRuleContext() {
        return null;
    }
}
