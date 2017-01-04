package de.tud.cs.se.ds.psec.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
    // Parser Tests
    de.tud.cs.se.ds.psec.parser.ParserTest.class,
    de.tud.cs.se.ds.psec.parser.SimpleParserTest.class,
    // Compiler Tests
    de.tud.cs.se.ds.psec.compiler.SimpleCompilerFunctionalTests.class,
    de.tud.cs.se.ds.psec.compiler.MethodCallFunctionalTests.class,
    de.tud.cs.se.ds.psec.compiler.InheritanceFunctionalTest.class,
})

/**
 * Test suite for key.compilation.
 *
 * @author Dominic Scheurer
 */
public class TestAlfred {

}
