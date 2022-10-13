package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.FreeLDT;
import de.uka.ilkd.key.logic.Name;

import javax.annotation.Nullable;
import java.util.List;

public class FreeLiteral extends Literal {
    public final static FreeLiteral INSTANCE = new FreeLiteral(null, null);

    public FreeLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }

    @Override
    public void visit(Visitor v) {
        // TODO Auto-generated method stub

    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_FREE_ADT);
    }

    @Override
    public Name getLDTName() {
        return FreeLDT.NAME;
    }

}