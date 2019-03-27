package edu.kit.iti.formal.psdbg.interpreter;

import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.TransformAst;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Test;

import java.io.IOException;
import java.util.List;

/**
 * Created by weigl on 22.06.2017.
 */
public class ControlFlowVisitorTest {
    @Test
    public void test() throws IOException {
        ScriptLanguageParser a = Facade.getParser(CharStreams.fromStream(
                getClass().getResourceAsStream("/edu/kit/iti/formal/psdbg/interpreter/simple1.txt")));
        List<ProofScript> scripts = (List<ProofScript>) a.start().accept(new TransformAst());
        ProofScript s = scripts.get(0);
        //ControlFlowVisitor pfv = new ControlFlowVisitor(new DefaultLookup());
        //s.accept(pfv);
        //System.out.println(pfv.asdot());
    }

}