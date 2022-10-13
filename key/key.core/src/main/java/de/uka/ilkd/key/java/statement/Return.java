package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

public class Return extends ExpressionJumpStatement {
    public Return(PositionInfo pi, List<Comment> comments, @Nonnull Expression expression) {
        super(pi, comments, expression);
    }

    /**
     * Expression jump statement.
     *
     * @param expr an Expression used to jump
     */
    public Return(@Nonnull Expression expr) {
        super(expr);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes.
     *                 May contain: 	an Expression (as expression of the
     *                 ExpressionJumpStatement),
     *                 Comments
     */
    public Return(ExtList children) {
        super(children);
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnReturn(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printReturn(this);
    }
}