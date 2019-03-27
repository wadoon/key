package edu.kit.iti.formal.psdbg.parser;

import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class ASTDiffTest {

    private static final String PREFIX = "src/test/resources/edu/kit/iti/formal/psdbg/parser";

    @Test
    public void testDiff1() throws IOException {
        List<ProofScript> o = Facade.getAST(new File(PREFIX, "test_diff_1.kps"));
        ASTDiff astDiff = new ASTDiff();
        ProofScript res = astDiff.diff(o.get(0), o.get(1));

        assertEquals(
                o.get(2).accept(new PrettyPrinter()),
                res.accept(new PrettyPrinter())
        );
    }


}