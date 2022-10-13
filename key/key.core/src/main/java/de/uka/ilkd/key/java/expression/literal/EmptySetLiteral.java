package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;

import javax.annotation.Nullable;
import java.util.List;


public class EmptySetLiteral extends Literal {
    public static final EmptySetLiteral LOCSET = new EmptySetLiteral(null, null);

    public EmptySetLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }

    @Override
    public boolean equalsModRenaming(SourceElement o,
                                     NameAbstractionTable nat) {
        return o == this;
    }


    public void visit(Visitor v) {
        v.performActionOnEmptySetLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptySetLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        PrimitiveType type = PrimitiveType.JAVA_LOCSET;
        return javaServ.getJavaInfo().getKeYJavaType(type);
    }

    @Override
    public Name getLDTName() {
        return LocSetLDT.NAME;
    }
}
