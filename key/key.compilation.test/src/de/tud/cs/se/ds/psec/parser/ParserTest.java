package de.tud.cs.se.ds.psec.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.net.URL;
import java.util.ArrayList;
import java.util.Optional;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Before;
import org.junit.Test;

import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.util.ResourceManager;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Tests for the translation taclet parser. Parses the complete translation rule
 * base.
 *
 * @author Dominic Scheurer
 */
public class ParserTest {
    private static final String TRANSLATION_RULES_PATH = "/de/tud/cs/se/ds/psec/compiler/rules/javaTranslationRules.cmp";

    private TranslationDefinitions definitions;

    @Before
    public void setUp() throws Exception {
        Optional<URL> maybeUrl = ResourceManager.instance().getResourceFile(
                TranslationTacletParser.class, TRANSLATION_RULES_PATH);

        if (!maybeUrl.isPresent()) {
            fail("Could not find translation rules path: "
                    + TRANSLATION_RULES_PATH);
        }

        definitions = new TranslationTacletParserFE(true).parse(maybeUrl.get());
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

        assertTrue("Rule is not applicable as expected", ifSplitDefn
                .isApplicable(new ApplicabilityCheckInput(2, null, null)));
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

    /**
     * Creates a {@link TranslationTacletParser} for the given input
     * {@link String}.
     * 
     * @param input
     *            The {@link String} to parse.
     * @return The {@link TranslationTacletParser} for the input.
     */
    static TranslationTacletParser setupParser(String input) {
        CharStream stream = new ANTLRInputStream(input);

        // Create the lexer
        TranslationTacletLexer lexer = new TranslationTacletLexer(stream);

        // Create a buffer of tokens pulled from the lexer
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // Create the parser
        TranslationTacletParser parser = new TranslationTacletParser(tokens);

        return parser;
    }

    /**
     * Loads the given proof file. Checks if the proof file exists and the proof
     * is not null, and fails if the proof could not be loaded.
     *
     * @param proofFileName
     *            The file name of the proof file to load.
     * @return The loaded proof.
     */
    static Proof loadProof(String proofFileName) {
        File proofFile = new File(proofFileName);
        assertTrue(proofFile.exists());

        try {
            KeYEnvironment<?> environment = KeYEnvironment.load(
                    JavaProfile.getDefaultInstance(), proofFile, null, null,
                    null, true);
            Proof proof = environment.getLoadedProof();
            assertNotNull(proof);

            return proof;
        } catch (ProblemLoaderException e) {
            fail("Proof could not be loaded:\n" + e.getMessage());
            return null;
        }
    }

}
