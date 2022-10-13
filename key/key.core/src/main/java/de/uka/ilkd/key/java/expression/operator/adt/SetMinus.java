package de.uka.ilkd.key.java.expression.operator.adt;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

public class SetMinus extends BinaryOperator {
    public SetMinus(PositionInfo pi, List<Comment> comments, @Nonnull Expression lhs, @Nonnull Expression rhs) {
        super(pi, comments, lhs, rhs);
    }

    public SetMinus(ExtList children) {
        super(children);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSetMinus(this);
    }


    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSetMinus(this);
    }

}