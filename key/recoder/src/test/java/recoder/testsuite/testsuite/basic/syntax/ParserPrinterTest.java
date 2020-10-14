package recoder.testsuite.testsuite.basic.syntax;

import java.util.List;

import junit.framework.Assert;
import junit.framework.TestCase;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.convenience.Format;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.testsuite.testsuite.basic.BasicTestsSuite;

public class ParserPrinterTest extends TestCase {

    public void testParserPrinter() throws ParserException {
        SourceFileRepository sfr = BasicTestsSuite.config.getSourceFileRepository();
        ProgramFactory pf = BasicTestsSuite.config.getProgramFactory();
        List<CompilationUnit> units = sfr.getCompilationUnits();
        for (int i = 0; i < units.size(); i += 1) {
            CompilationUnit cu = units.get(i);
            String buffer1 = cu.toSource();
            CompilationUnit cv = pf.parseCompilationUnit(buffer1);
            if (!ProgramElement.STRUCTURAL_EQUALITY.equals(cu, cv)) {
                Assert.fail("Printed tree of " + Format.toString("%u", cu) + " has changed its structure");
            }
            String buffer2 = cv.toSource();
            if (!buffer1.equals(buffer2)) {
                Assert.fail(Format.toString("Reprint of parsed %u differs", cu));
            }
        }
    }
}
