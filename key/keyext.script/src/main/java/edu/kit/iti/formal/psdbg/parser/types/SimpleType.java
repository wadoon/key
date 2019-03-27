package edu.kit.iti.formal.psdbg.parser.types;

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


import javax.annotation.Nullable;

/**
 * Represents the possible types (including scriptVarTypes).
 * <p>
 * Created at 30.04.2017
 *     INT("\\term int"),
 BOOL("\\term bool"),
 ANY("\\term any"),
 INT_ARRAY("\\term int[]"),
 OBJECT("\\term Object"),
 HEAP("\\term Heap"),
 FIELD("\\term Field"),
 LOCSET("\\term LocSet"),
 FORMULA("\\formula"),
 SEQ("\\term Seq");
 * @author Sarah Grebing
 */
public enum SimpleType implements Type {
    STRING("string", "string"),
    //ANY("any", "any"),
    PATTERN("pattern", null),
    INT("int", "int"),
    BOOL("bool", "bool"),
    /*NULL("null", interpreterSort),
    FORMULA("formula", interpreterSort),
    SEQ("Seq", interpreterSort)*/;


    private final String symbol;
    private @Nullable  final String interpreterSort;

    SimpleType(String symbol, @Nullable String interpreterSort) {
        this.symbol = symbol;
        this.interpreterSort = interpreterSort;
    }



    @Override
    public String symbol() {
        return symbol;
    }

    @Override
    public String interpreterSort() {
        return interpreterSort;
    }
}
