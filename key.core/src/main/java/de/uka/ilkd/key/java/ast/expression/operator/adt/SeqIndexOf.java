package de.uka.ilkd.key.java.ast.expression.operator.adt;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.Expression;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.collection.ImmutableArray;

/**
 * Represents a function giving the index of some element in a sequence (if it exists).
 *
 * @author bruns
 *
 */
public class SeqIndexOf extends Operator {

    public SeqIndexOf(PositionInfo pi, List<Comment> c, Expression child) {
        super(pi, c, new ImmutableArray<>(child));
    }


    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnSeqIndexOf(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return javaServ.getJavaInfo().getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT);
    }


    @Override
    public int getNotation() {
        return Operator.PREFIX;
    }

}