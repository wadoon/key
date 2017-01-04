package de.tud.cs.se.ds.psec.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;

import org.junit.Before;
import org.junit.Test;

import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCheckInput;
import de.tud.cs.se.ds.psec.parser.ast.ApplicabilityCondition;
import de.tud.cs.se.ds.psec.parser.ast.GlobalLabelInitialization;
import de.tud.cs.se.ds.psec.parser.ast.LabelNameOrNameDecl;
import de.tud.cs.se.ds.psec.parser.ast.LabelUnaryBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.LabeledBytecodeInstr;
import de.tud.cs.se.ds.psec.parser.ast.NameDecl;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinition;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * Tests for the translation taclet parser. Independent of the translation rule
 * base.
 *
 * @author Dominic Scheurer
 */
public class SimpleParserTest {
    private Services services;

    @Before
    public void setUp() throws Exception {
        services = ParserTest.loadProof("resources/testcase/dummy.key")
                .getServices();
    }

    @Test
    public void testNegatedArithmeticExpr() {
        String testStr = "\\condition (!#num-children >= 2)";

        TranslationTacletParser parser = ParserTest.setupParser(testStr);
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

        TranslationTacletParser parser = ParserTest.setupParser(sb.toString());
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

    @Test
    public void testSimpleTypeExpr() {
        String testStr = "\\condition (isSimpleType(#se))";

        TranslationTacletParser parser = ParserTest.setupParser(testStr);
        ApplicabilityCondition parsedCondition = new TranslationTacletParserFE(
                true).visitCondition(parser.condition());

        HashMap<String, Object> map = new HashMap<>();
        map.put("#se", new LocationVariable(new ProgramElementName("v"),
                services.getJavaInfo().getKeYJavaType("int")));

        assertTrue(parsedCondition.isApplicable(new ApplicabilityCheckInput(0,
                new RuleInstantiations(map), services)));

        map.put("#se", new LocationVariable(new ProgramElementName("v"),
                services.getJavaInfo().getKeYJavaType("java.lang.Object")));

        assertFalse(parsedCondition.isApplicable(new ApplicabilityCheckInput(0,
                new RuleInstantiations(map), services)));
    }

    @Test
    public void testStrEqualsExpr() {
        String testStr1 = "\\condition ( strEquals (#se,  \"TRUE\" ))";
        String testStr2 = "\\condition (!strEquals (#se,  \"TRUE\" ))";
        String testStr3 = "\\condition ( strEquals (#se1, \"FALSE\"))";

        HashMap<String, Object> map = new HashMap<>();
        map.put("#se", services.getTermBuilder().TRUE());
        map.put("#se1", services.getTermBuilder().FALSE());

        TranslationTacletParser parser = ParserTest.setupParser(testStr1);
        ApplicabilityCondition parsedCondition = new TranslationTacletParserFE(
                true).visitCondition(parser.condition());
        assertTrue(parsedCondition.isApplicable(new ApplicabilityCheckInput(0,
                new RuleInstantiations(map), services)));

        parser = ParserTest.setupParser(testStr2);
        parsedCondition = new TranslationTacletParserFE(true)
                .visitCondition(parser.condition());
        assertFalse(parsedCondition.isApplicable(new ApplicabilityCheckInput(0,
                new RuleInstantiations(map), services)));
        
        parser = ParserTest.setupParser(testStr3);
        parsedCondition = new TranslationTacletParserFE(true)
                .visitCondition(parser.condition());
        assertTrue(parsedCondition.isApplicable(new ApplicabilityCheckInput(0,
                new RuleInstantiations(map), services)));
    }

    @Test
    public void testNameFunctionAndGlobalLabels() {
        String test1a = "\\name (#loc, \"_exit\")";
        String test1b = "l0";
        String test2 = "\\newGlobalLabel (" + test1a + ")";
        String test3 = "\\globalLabel (" + test1a + ")";
        String test4 = test3 + ": #child-1";
        String test5 = "GOTO " + test3;

        final TranslationTacletParserFE parserFE = //
                new TranslationTacletParserFE(true);

        HashMap<String, Object> map = new HashMap<>();
        map.put("#loc", new LocationVariable(new ProgramElementName("x"),
                services.getJavaInfo().getKeYJavaType("boolean")));

        RuleInstantiations instantiations = new RuleInstantiations(map);

        TranslationTacletParser parser = ParserTest.setupParser(test1a);
        NameDecl nameDecl = parserFE.visitName_decl(parser.name_decl());
        assertEquals("x_exit", nameDecl.getName(instantiations));

        parser = ParserTest.setupParser(test1a);
        LabelNameOrNameDecl labelNameOrNameDecl = parserFE
                .visitLabel_name_or_name_decl(parser.label_name_or_name_decl());
        assertEquals("x_exit", labelNameOrNameDecl.getName(instantiations));

        parser = ParserTest.setupParser(test1b);
        labelNameOrNameDecl = parserFE
                .visitLabel_name_or_name_decl(parser.label_name_or_name_decl());
        assertEquals("l0", labelNameOrNameDecl.getName(instantiations));

        parser = ParserTest.setupParser(test2);
        assertTrue(parserFE.visitInstruction(
                parser.instruction()) instanceof GlobalLabelInitialization);

        parser = ParserTest.setupParser(test3);
        labelNameOrNameDecl = parserFE
                .visitGlobal_label_ref(parser.global_label_ref());
        assertEquals("x_exit", labelNameOrNameDecl.getName(instantiations));

        parser = ParserTest.setupParser(test4);
        LabeledBytecodeInstr instr = parserFE
                .visitLabeled_bytecode_instr(parser.labeled_bytecode_instr());
        assertEquals("x_exit: ChildCall", instr.toString(instantiations));

        parser = ParserTest.setupParser(test5);
        assertTrue(parserFE.visitInstruction(
                parser.instruction()) instanceof LabelUnaryBytecodeInstr);
    }

}
