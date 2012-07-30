package de.uka.ilkd.keyabs.abs;

import java.io.IOException;

import abs.frontend.analyser.SemanticError;
import abs.frontend.ast.Model;
import abs.frontend.ast.ModuleDecl;
import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class ABSReader implements JavaReader {

	private static final String CONCRETE_MODULE_NAME = "ABS_PARSER_NORMAL_MODULE";
	private static final String CONCRETE_MODULE = "module " + CONCRETE_MODULE_NAME + ";";

    @Override
    public JavaBlock readBlockWithEmptyContext(String s, IServices services) {
        return null;
    }

    @Override
    public JavaBlock readBlockWithProgramVariables(Namespace<IProgramVariable> varns, IServices services, String s) {
        String blockStr = CONCRETE_MODULE + "\n import * from PingPong; " + s;
        try {
            Model m = ((ABSServices)services).getProgramInfo().parseInContext(blockStr);                    
            ModuleDecl module = null;
            for (ModuleDecl md : m.getModuleDecls()) {
            	if (md.getName().equals(CONCRETE_MODULE_NAME)) {
            		module = md;
            		break;
            	}
            }
            
            System.out.println(" Errors: "+m.getErrors());
            
            for (SemanticError se : m.getErrors()) {
                System.out.println(se.getHelpMessage() + " : " + se.getFileName() + " : " + se.getMsgString());
            }
            System.out.println(module.getBlock() + " Errors: "+m.getErrors());
           
            AbstractABS2KeYABSConverter converter = new ConcreteABS2KeYABSConverter(varns, services);
            
            ABSStatementBlock block = converter.convert(module.getBlock());

            System.out.println("Converted " + block);

            return JavaBlock.createJavaBlock(block);
        } catch (IOException e) {
            throw new ConvertException("Failed to parse ABS block.", e);
        } catch (Exception e) {
            throw new ConvertException("Failed to parse ABS block.", e);
        }
    }

}
