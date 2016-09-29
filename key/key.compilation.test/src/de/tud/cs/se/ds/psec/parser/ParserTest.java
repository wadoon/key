package de.tud.cs.se.ds.psec.parser;

import java.net.URL;
import java.util.ArrayList;

import org.junit.Test;

import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
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

        definitions = new TranslationTacletParserFE().parse(url);
    }

    @Test
    public void testRulesExist() {
        ArrayList<TranslationDefinition> defn = definitions
                .getDefinitionsFor("IfSplit");

        assertNotNull("No rule for IfSplit", defn);
        assertEquals("There should be two rules for IfSplit", defn.size(), 2);
    }

    @Test
    public void testRuleFiltering() {
        assertNotNull("No single rule for IfSplit with two children",
                definitions.getDefinitionFor("IfSplit",
                        new ApplicabilityCheckInput(2)));
    }

    @Test
    public void testApplicability() {
        TranslationDefinition ifSplitDefn = definitions
                .getDefinitionFor("IfSplit", new ApplicabilityCheckInput(2));
        
        assertNotNull(ifSplitDefn);

        assertTrue("Rule is not applicable as expected",
                ifSplitDefn.isApplicable(new ApplicabilityCheckInput(2)));
    }

    @Test
    public void testSameTranslationForIfSplitAndIfElseSplit() {
        TranslationDefinition ifSplitDefn = definitions
                .getDefinitionFor("IfSplit", new ApplicabilityCheckInput(2));
        TranslationDefinition ifElseSplitDefn = definitions.getDefinitionFor(
                "IfElseSplit", new ApplicabilityCheckInput(2));

        assertNotNull(ifSplitDefn);
        assertNotNull(ifElseSplitDefn);

        assertEquals(
                "Different rules for IfSplit and IfElseSplit, equal expected",
                ifSplitDefn, ifElseSplitDefn);
    }

}
