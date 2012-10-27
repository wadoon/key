package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public class EVal
        extends Val {

    public final Exp exp_;

    public EVal(Exp p1) {

        exp_ = p1;
    }

    public <R, A> R accept(
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Val.Visitor<R, A> v,
            A arg) {

        return v.visit(this, arg);
    }

    public boolean equals(Object o) {

        if (this == o)
            return true;
        if (o instanceof de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EVal) {
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EVal x =
                    (de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EVal) o;
            return this.exp_.equals(x.exp_);
        }
        return false;
    }

    public int hashCode() {

        return this.exp_.hashCode();
    }

}
