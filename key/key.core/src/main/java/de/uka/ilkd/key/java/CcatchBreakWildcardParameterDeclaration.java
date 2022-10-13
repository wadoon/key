package de.uka.ilkd.key.java;

import java.io.IOException;
import java.util.List;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * A "\Break *" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchBreakWildcardParameterDeclaration
        extends CcatchNonstandardParameterDeclaration {

    public CcatchBreakWildcardParameterDeclaration(PositionInfo pi, List<Comment> comments) {
        super(pi, comments);
    }

    public CcatchBreakWildcardParameterDeclaration(ExtList children) {
        super(null,null);
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
        v.performActionOnCcatchBreakWildcardParameterDeclaration(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printCcatchBreakWildcardParameterDeclaration(this);
    }

}
