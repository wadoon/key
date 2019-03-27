package edu.kit.iti.formal.psdbg.interpreter;

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


import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.NotWelldefinedException;
import edu.kit.iti.formal.psdbg.TestHelper;
import edu.kit.iti.formal.psdbg.parser.ast.Expression;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;

@RunWith(Parameterized.class)
public class EvalTest {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getGoodExpressions() throws IOException {
        return TestHelper.loadLines("eval.txt", 2);
    }

    @Parameterized.Parameter(0)
    public String testExpression;

    @Parameterized.Parameter(1)
    public String expResult;


    @Test
    public void test() throws IOException, NotWelldefinedException {
        Expression e_is = TestHelper.toExpr(testExpression);
        Expression e_exp = TestHelper.toExpr(expResult);

        VariableAssignment s = createAssignments();
        Evaluator<String> evaluator = new Evaluator<>(s, new GoalNode<>(null));

        Value is = evaluator.eval(e_is);
        Value exp = evaluator.eval(e_exp);

        Assert.assertEquals(exp,is);
    }

    public static VariableAssignment createAssignments() {
        VariableAssignment va = new VariableAssignment();
        va.declare("a",  SimpleType.INT);
        va.assign("a", Value.from(10));
        va.declare("b",  SimpleType.INT);
        va.assign("b", Value.from(2));

        va.declare("c",  SimpleType.INT);
        va.assign("c", Value.from(10));

        va.declare("d",  SimpleType.INT);
        va.assign("d", Value.from(10));

        return va;
    }

}
