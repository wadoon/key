package edu.kit.iti.formal.psdbg.parser;

import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.Parameters;



public class SavepointVisitor extends DefaultASTVisitor {


    @Override
    public Parameters visit(CallStatement call) {
        if (call.getCommand().toString().equals("save")) {
            Parameters param = call.getParameters().copy();
            return param;
        } else {
            return null;
        }

    }

}
