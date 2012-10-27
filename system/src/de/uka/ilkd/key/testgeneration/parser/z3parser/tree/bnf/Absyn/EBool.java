package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public class EBool
        extends Exp {

    public final Bool bool_;

    public EBool(Bool p1) {

        bool_ = p1;
    }

    public <R, A> R accept(
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Exp.Visitor<R, A> v,
            A arg) {

        return v.visit(this, arg);
    }

    public boolean equals(Object o) {

        if (this == o)
            return true;
        if (o instanceof de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EBool) {
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EBool x =
                    (de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EBool) o;
            return this.bool_.equals(x.bool_);
        }
        return false;
    }

    public int hashCode() {

        return this.bool_.hashCode();
    }

}
