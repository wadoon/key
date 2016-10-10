package de.tud.cs.se.ds.psec.parser;

import java.net.URL;
import java.util.ArrayList;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Test;

import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCondition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.util.ResourceManager;
import junit.framework.TestCase;

/**
 * Tests for the translation taclet parser.
 *
 * @author Dominic Scheurer
 */
public class ParserTest extends TestCase {
    private static final String TRANSLATION_RULES_PATH = "/de/tud/cs/se/ds/psec/compiler/rules/javaTranslationRules.cmp";

    private TranslationDefinitions definitions;

    @Override
    protected void setUp() throws Exception {
        URL url = ResourceManager.instance().getResourceFile(
                TranslationTacletParser.class, TRANSLATION_RULES_PATH);

        definitions = new TranslationTacletParserFE(true).parse(url);
    }

    @Test
    public void testRulesExist() {
        ArrayList<TranslationDefinition> defn = definitions
                .getDefinitionsFor("ifSplit");

        assertNotNull("No rule for ifSplit", defn);
        assertEquals("There should be two rules for ifSplit", defn.size(), 2);
    }

    @Test
    public void testRuleFiltering() {
        assertNotNull("No single rule for ifSplit with two children",
                definitions.getDefinitionFor("ifSplit",
                        new ApplicabilityCheckInput(2, null, null)));
    }

    @Test
    public void testApplicability() {
        TranslationDefinition ifSplitDefn = definitions.getDefinitionFor(
                "ifSplit", new ApplicabilityCheckInput(2, null, null));

        assertNotNull(ifSplitDefn);

        assertTrue("Rule is not applicable as expected",
                ifSplitDefn.isApplicable(new ApplicabilityCheckInput(2, null, null)));
    }

    @Test
    public void testSameTranslationForIfSplitAndIfElseSplit() {
        TranslationDefinition ifSplitDefn = definitions.getDefinitionFor(
                "ifSplit", new ApplicabilityCheckInput(2, null, null));
        TranslationDefinition ifElseSplitDefn = definitions.getDefinitionFor(
                "ifElseSplit", new ApplicabilityCheckInput(2, null, null));

        assertNotNull(ifSplitDefn);
        assertNotNull(ifElseSplitDefn);

        assertEquals(
                "Different rules for ifSplit and ifElseSplit, equal expected",
                ifSplitDefn, ifElseSplitDefn);
    }

    @Test
    public void testNegatedArithmeticExpr() {
        String testStr = "\\condition (!#num-children >= 2)";

        TranslationTacletParser parser = setupParser(testStr);
        ApplicabilityCondition parsedCondition = new TranslationTacletParserFE(
                true).visitCondition(parser.condition());

        assertTrue(parsedCondition
                .isApplicable(new ApplicabilityCheckInput(0, null, null)));
        assertTrue(parsedCondition
                .isApplicable(new ApplicabilityCheckInput(1, null, null)));
        assertFalse(parsedCondition
                .isApplicable(new ApplicabilityCheckInput(2, null, null)));
        assertFalse(parsedCondition
                .isApplicable(new ApplicabilityCheckInput(3, null, null)));
    }

    @Test
    public void testMultipleConditions() {
        StringBuilder sb = new StringBuilder();

        //@formatter:off
        sb
            .append("test {")
            .append("  \\taclets (\"testTaclet\")")
            // This should define an unsatisfiable condition
            .append("  \\condition (!#num-children >= 2)")
            .append("  \\condition ( #num-children >= 2)")
            .append("  \\translation ( RETURN )")
            .append("}");
        //@formatter:on

        TranslationTacletParser parser = setupParser(sb.toString());
        TranslationDefinition parsedDefinition = new TranslationTacletParserFE(
                true).visitDefinition(parser.definition());

        assertFalse(parsedDefinition
                .isApplicable(new ApplicabilityCheckInput(0, null, null)));
        assertFalse(parsedDefinition
                .isApplicable(new ApplicabilityCheckInput(1, null, null)));
        assertFalse(parsedDefinition
                .isApplicable(new ApplicabilityCheckInput(2, null, null)));
        assertFalse(parsedDefinition
                .isApplicable(new ApplicabilityCheckInput(3, null, null)));
    }

    // TODO: Add test for "isSimpleType(...)". Need to have access to a Services
    // object for that.

    /**
     * Creates a {@link TranslationTacletParser} for the given input
     * {@link String}.
     * 
     * @param input
     *            The {@link String} to parse.
     * @return The {@link TranslationTacletParser} for the input.
     */
    private TranslationTacletParser setupParser(String input) {
        CharStream stream = new ANTLRInputStream(input);

        // Create the lexer
        TranslationTacletLexer lexer = new TranslationTacletLexer(stream);

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        TranslationTacletParser parser = new TranslationTacletParser(tokens);

        return parser;
    }

}
