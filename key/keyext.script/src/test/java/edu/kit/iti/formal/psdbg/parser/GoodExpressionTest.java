package edu.kit.iti.formal.psdbg.parser;

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



import edu.kit.iti.formal.psdbg.TestHelper;
import edu.kit.iti.formal.psdbg.parser.ast.Expression;
import edu.kit.iti.formal.psdbg.parser.ast.Signature;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;

@RunWith(Parameterized.class)
public class GoodExpressionTest {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getGoodExpressions() throws IOException {
        return TestHelper.loadLines("scripts/goodexpr.txt", 1);
    }

    @Parameterized.Parameter
    public String testExpression;


    @Test
    public void test() throws IOException, NotWelldefinedException {
        ScriptLanguageParser slp = TestHelper.getParser(testExpression);
        ScriptLanguageParser.ExpressionContext e = slp.expression();
        Assert.assertEquals(0, slp.getNumberOfSyntaxErrors());

        Expression expr = (Expression) e.accept(new TransformAst());
        Signature s = createSignature();
        System.out.println(expr.getType(s));
    }

    public static Signature createSignature() {
        Signature s = new Signature();
        s.put(new Variable("a"), SimpleType.BOOL);
        s.put(new Variable("b"), SimpleType.BOOL);
        s.put(new Variable("c"), SimpleType.BOOL);
        s.put(new Variable("i"), SimpleType.INT);
        s.put(new Variable("j"), SimpleType.INT);
        s.put(new Variable("k"), SimpleType.INT);
        return s;
    }

}
