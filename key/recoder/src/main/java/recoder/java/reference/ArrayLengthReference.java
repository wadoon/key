package recoder.java.reference;

import recoder.ModelException;
import recoder.ProgramFactory;
import recoder.java.*;
import recoder.list.generic.ASTList;

/**
 * TODO
 * @author Alexander Weigl
 * @version 1 (11/10/21)
 */
public class ArrayLengthReference implements Expression {
    public ArrayLengthReference(ReferencePrefix tmpResult) {

    }

    public ProgramElement getReferencePrefix() {
        return null;
    }

    @Override
    public void validate() throws ModelException {

    }

    @Override
    public ExpressionContainer getExpressionContainer() {
        return null;
    }

    @Override
    public void setExpressionContainer(ExpressionContainer c) {

    }

    @Override
    public SourceElement getFirstElement() {
        return null;
    }

    @Override
    public SourceElement getLastElement() {
        return null;
    }

    @Override
    public Position getStartPosition() {
        return null;
    }

    @Override
    public Position getEndPosition() {
        return null;
    }

    @Override
    public Position getRelativePosition() {
        return null;
    }

    @Override
    public void setStartPosition(Position p) {

    }

    @Override
    public void setEndPosition(Position p) {

    }

    @Override
    public void setRelativePosition(Position p) {

    }

    @Override
    public ProgramFactory getFactory() {
        return null;
    }

    @Override
    public void accept(SourceVisitor v) {

    }

    @Override
    public String toSource() {
        return null;
    }

    @Override
    public Expression deepClone() {
        return null;
    }

    @Override
    public int getID() {
        return 0;
    }

    @Override
    public NonTerminalProgramElement getASTParent() {
        return null;
    }

    @Override
    public ASTList<Comment> getComments() {
        return null;
    }

    @Override
    public void setComments(ASTList<Comment> list) {

    }
}
