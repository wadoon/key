package de.uka.ilkd.key.testgeneration;

import java.util.HashMap;
import java.util.StringTokenizer;
import org.junit.Test;

import de.uka.ilkd.key.testgeneration.parser.z3parser.api.Z3ModelParser;
import de.uka.ilkd.key.testgeneration.parser.z3parser.api.Z3Visitor.ValueContainer;



import junit.framework.TestCase;

/**
 * Verify that the parser works as intended
 * 
 * @author christopher
 *
 */
public class TestParsing extends KeYTestGenTest {

    String rawModel = "";
    HashMap<String, ValueContainer> refinedModel = new HashMap<String, ValueContainer>();

    @Test
    public void testParsingInts() throws Exception {

        rawModel = 
                "(model   " +
                        "(define-fun i_2 () Int    (- 1))" +
                        "(define-fun j_3 () Int    1)" +
                        "(define-fun k_4 () Int    1245)" +
                        "(define-fun l_5 () Int    6755545)" +
                        "(define-fun m_6 () Int    (- 4234))" +
                        ")";;


                        refinedModel = Z3ModelParser.parseModel(rawModel);

                        assertTrue(refinedModel.get("j").getName().equals("j"));
                        assertTrue(refinedModel.get("j").getType().equals(ValueContainer.Type.INTEGER));
                        assertTrue(refinedModel.get("j").getValue().equals(1));

                        assertTrue(refinedModel.get("i").getName().equals("i"));
                        assertTrue(refinedModel.get("i").getType().equals(ValueContainer.Type.INTEGER));
                        assertTrue(refinedModel.get("i").getValue().equals(-1));

                        assertTrue(refinedModel.get("k").getName().equals("k"));
                        assertTrue(refinedModel.get("k").getType().equals(ValueContainer.Type.INTEGER));
                        assertTrue(refinedModel.get("k").getValue().equals(1245));

                        assertTrue(refinedModel.get("l").getName().equals("l"));
                        assertTrue(refinedModel.get("l").getType().equals(ValueContainer.Type.INTEGER));
                        assertTrue(refinedModel.get("l").getValue().equals(6755545));

                        assertTrue(refinedModel.get("m").getName().equals("m"));
                        assertTrue(refinedModel.get("m").getType().equals(ValueContainer.Type.INTEGER));
                        assertTrue(refinedModel.get("m").getValue().equals(-4234));
    }
}
