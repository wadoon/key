package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import java.io.IOException;
import java.util.List;

/**
 * A "\Continue" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueParameterDeclaration
        extends CcatchNonstandardParameterDeclaration {

    public CcatchContinueParameterDeclaration(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }

    public CcatchContinueParameterDeclaration(ExtList children) {
        super(null, null);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchContinueParameterDeclaration(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printCcatchContinueParameterDeclaration(this);
    }

}
