package de.uka.ilkd.key.java.ast.expression.operator.adt;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Expression;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class SeqConcat extends BinaryOperator {

    public SeqConcat(PositionInfo pi, List<Comment> c, Expression child, Expression b) {
        super(pi, c, child, b);
    }

    public SeqConcat(Expression seq1, Expression seq2) {
        super(seq1, seq2);
    }

    public SeqConcat(ExtList changeList) {
        super(changeList);
    }


    public int getPrecedence() {
        return 0;
    }


    public int getNotation() {
        return Operator.PREFIX;
    }


    public void visit(Visitor v) {
        v.performActionOnSeqConcat(this);
    }

}