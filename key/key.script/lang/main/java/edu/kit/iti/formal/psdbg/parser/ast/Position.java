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


import lombok.Data;
import lombok.RequiredArgsConstructor;
import lombok.Value;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 */
@Data
@Value
@RequiredArgsConstructor
public class Position implements Copyable<Position> {
    private final int offset;
    private final int lineNumber;
    private final int charInLine;

    public Position() {
        this(-1, -1, -1);
    }

    public static Position start(Token token) {
        return new Position(
                token.getStartIndex(),
                token.getLine(),
                token.getCharPositionInLine());
    }

    public static Position end(Token token) {
        return new Position(
                token.getStopIndex(),
                token.getLine(),
                token.getCharPositionInLine());
    }

    /**
     * Determines the starts position from the given {@link ParserRuleContext}.
     *
     * @param token
     * @return null if the given token is null.
     */
    public static Position start(ParserRuleContext token) {
        if (token == null)
            return null;
        return start(token.start);
    }

    public static Position end(ParserRuleContext token) {
        if (token == null) return null;
        return end(token.stop);
    }

    @Override
    public Position copy() {
        return new Position(offset, lineNumber, charInLine);
    }
}
