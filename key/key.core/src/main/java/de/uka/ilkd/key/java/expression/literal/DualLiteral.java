package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.DualLDT;
import de.uka.ilkd.key.logic.Name;

public class DualLiteral extends Literal {

    final String value;

    public DualLiteral(double d) {
        this.value = "(" + d + "d, " + d + "r)";
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_DOUBLE);
    }

    @Override
    public Name getLDTName() {
        return DualLDT.NAME;
    }
}
