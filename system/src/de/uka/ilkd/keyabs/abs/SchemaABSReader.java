package de.uka.ilkd.keyabs.abs;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.ASTNode;
import abs.frontend.ast.Model;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.SchemaJavaReader;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;

public class SchemaABSReader implements SchemaJavaReader {

    private static final String SCHEMA_MODULE = "module SCHEMA_TACLET_READ_MODULE;";
    private Namespace schemaVariables = new Namespace();;
    
    private void printTree(ASTNode node) {
        for (int i = 0; i<node.getNumChild(); i++) {
            System.out.println(node.value + ":" + node + ":" + node.getClass().getSimpleName());
            printTree(node.getChild(i));
        }
    }
    
    @Override
    public JavaBlock readBlockWithEmptyContext(String s) {
        String blockStr = SCHEMA_MODULE + " \n " + s;
        
        CoreAbsBackend absReader = new CoreAbsBackend();
        absReader.setWithStdLib(false);
        try {
            Model m = absReader.parse(File.createTempFile("taclet_", ".keyabs"), blockStr, new StringReader(blockStr));
            System.out.println(m.getMainBlock());
            AbstractABS2KeYABSConverter converter = new SchemaABS2KeYABSConverter(schemaVariables);
            ABSStatementBlock block = converter.convert(m.getMainBlock());
            
            System.out.println("Converted " + block);
            
            return JavaBlock.createJavaBlock(block);
        } catch (IOException e) {
            throw new ConvertException("Failed to parser schema block of taclet.", e);
        } catch (Exception e) {
            throw new ConvertException("Failed to parser schema block of taclet.", e);
        }
    }

    @Override
    public JavaBlock readBlockWithProgramVariables(Namespace varns, String s) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void setSVNamespace(Namespace ns) {
        schemaVariables = ns;
    }

}
