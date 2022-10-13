package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;

import javax.annotation.Nullable;
import java.util.List;


public class EmptySeqLiteral extends Literal {
    public static final EmptySeqLiteral INSTANCE = new EmptySeqLiteral(null, null);

    public EmptySeqLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }

    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        return o == this || o.getClass() == getClass();
    }


    public void visit(Visitor v) {
        v.performActionOnEmptySeqLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptySeqLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }

    @Override
    public Name getLDTName() {
        return SeqLDT.NAME;
    }
}
