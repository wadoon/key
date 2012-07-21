package de.uka.ilkd.keyabs.abs;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.Model;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;

public class ABSReader implements JavaReader {

    private static final String CONCRETE_MODULE = "module ABS_PARSER_NORMAL_MODULE;";

    @Override
    public JavaBlock readBlockWithEmptyContext(String s) {
        return null;
    }

    @Override
    public JavaBlock readBlockWithProgramVariables(Namespace varns, String s) {
        String blockStr = CONCRETE_MODULE + " \n " + s;

        CoreAbsBackend absReader = new CoreAbsBackend();
        absReader.setWithStdLib(false);
        try {
            Model m = absReader.parse(File.createTempFile("taclet_", ".keyabs"), blockStr, new StringReader(blockStr));
            System.out.println(m.getMainBlock());
            AbstractABS2KeYABSConverter converter = new ConcreteABS2KeYABSConverter(varns);
            ABSStatementBlock block = converter.convert(m.getMainBlock());

            System.out.println("Converted " + block);

            return JavaBlock.createJavaBlock(block);
        } catch (IOException e) {
            throw new ConvertException("Failed to parser schema block of taclet.", e);
        } catch (Exception e) {
            throw new ConvertException("Failed to parser schema block of taclet.", e);
        }
    }

}
