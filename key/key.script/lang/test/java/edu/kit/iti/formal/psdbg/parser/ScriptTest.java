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
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
@RunWith(Parameterized.class)
public class ScriptTest {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getScripts() throws IOException {
        return TestHelper.getResourcesAsParameters("edu/kit/iti/formal/psdbg/parser/scripts");
    }

    @Parameterized.Parameter
    public File f;

    @Test public void parse() throws IOException {
        ScriptLanguageParser slp = TestHelper.getParser(f);
        slp.start();
        Assert.assertEquals(0, slp.getNumberOfSyntaxErrors());
    }

}
