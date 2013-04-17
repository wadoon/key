package de.uka.ilkd.keyabs.abs;

import java.io.File;
import java.io.IOException;
import java.io.StringReader;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.analyser.SemanticError;
import abs.frontend.ast.ASTNode;
import abs.frontend.ast.Model;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.SchemaJavaReader;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.keyabs.abs.ABSContextStatementBlock;
import de.uka.ilkd.keyabs.abs.ABSStatementBlock;
import de.uka.ilkd.keyabs.abs.AbstractABS2KeYABSConverter;
import de.uka.ilkd.keyabs.abs.SchemaABS2KeYABSConverter;

public class SchemaABSReader implements SchemaJavaReader {

    private static final String SCHEMA_MODULE = "module SCHEMA_TACLET_READ_MODULE;";
    private Namespace<IProgramVariable> schemaVariables = new Namespace<IProgramVariable>();;

    private void printTree(ASTNode node) {
        for (int i = 0; i < node.getNumChild(); i++) {
            /* System.out.println(node.value + ":" + node + ":"
                    + node.getClass().getSimpleName()); */
            printTree(node.getChild(i));
        }
    }

    @Override
    public JavaBlock readBlockWithEmptyContext(String s, IServices services) {
        String blockStr = s;
        boolean isContextBlock = false;
        if (blockStr.startsWith("{..") && blockStr.endsWith("...}")) {
            isContextBlock = true;
            blockStr = blockStr.replace("{..", "{");
            blockStr = blockStr.replace("...}", "}");
        }

        blockStr = SCHEMA_MODULE + " \n " + blockStr;

        CoreAbsBackend absReader = new CoreAbsBackend();
        absReader.setWithStdLib(false);
        absReader.setAllowIncompleteExpr(true);
        try {
            Model m = absReader.parse(
                    File.createTempFile("taclet_", ".keyabs"), blockStr,
                    new StringReader(blockStr));


            /* if (m.getErrors().size() > 0) {
                 System.out.println("ParseInput: " + blockStr);
                System.out.println(m.getMainBlock() + " Errors: " + m.getErrors().size());

                for (SemanticError se : m.getErrors()) {
                    System.out.println(se.getHelpMessage() + " : "
                            + se.getFileName() + " : " + se.getMsgString());
                }
            }*/
                
            AbstractABS2KeYABSConverter converter = new SchemaABS2KeYABSConverter(
                    schemaVariables, services);

            ABSStatementBlock block = converter.convert(m.getMainBlock());

            if (isContextBlock) {
                block = new ABSContextStatementBlock(block.getBody());
            }

            //System.out.println("Converted " + block);

            return JavaBlock.createJavaBlock(block);
        } catch (IOException e) {
            throw new ConvertException(
                    "Failed to parser schema block of taclet.", e);
        } catch (Exception e) {
            throw new ConvertException(
                    "Failed to parser schema block of taclet.", e);
        }
    }

    @Override
    public void setSVNamespace(Namespace ns) {
        schemaVariables = ns;
    }

    @Override
    public JavaBlock readBlockWithProgramVariables(
            Namespace<IProgramVariable> varns, IServices services, String s) {
        return null;
    }

}
