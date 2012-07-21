package de.uka.ilkd.keyabs.abs;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.analyser.SemanticError;
import abs.frontend.ast.Model;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;

public class ABSReader implements JavaReader {

    private static final String CONCRETE_MODULE = "module ABS_PARSER_NORMAL_MODULE;";

    @Override
    public JavaBlock readBlockWithEmptyContext(String s, IServices services) {
        return null;
    }

    @Override
    public JavaBlock readBlockWithProgramVariables(Namespace varns, IServices services, String s) {
        String blockStr = CONCRETE_MODULE + " \n " + s;

        CoreAbsBackend absReader = new CoreAbsBackend();
        //absReader.setWithStdLib(true);
        try {
            Model m = absReader.parse(File.createTempFile("taclet_", ".keyabs"), blockStr, new StringReader(blockStr));
            
            System.out.println(m.getMainBlock() + " Errors: "+m.getErrors());
            
            for (SemanticError se : m.getErrors()) {
                System.out.println(se.getHelpMessage() + " : " + se.getFileName() + " : " + se.getMsgString());
            }
           
            AbstractABS2KeYABSConverter converter = new ConcreteABS2KeYABSConverter(varns, services);
            
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
