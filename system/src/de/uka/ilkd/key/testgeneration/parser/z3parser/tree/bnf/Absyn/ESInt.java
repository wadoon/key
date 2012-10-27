package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public class ESInt
        extends Exp {

    public final Op op_;
    public final Integer integer_;

    public ESInt(Op p1, Integer p2) {

        op_ = p1;
        integer_ = p2;
    }

    public <R, A> R accept(
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Exp.Visitor<R, A> v,
            A arg) {

        return v.visit(this, arg);
    }

    public boolean equals(Object o) {

        if (this == o)
            return true;
        if (o instanceof de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.ESInt) {
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.ESInt x =
                    (de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.ESInt) o;
            return this.op_.equals(x.op_) && this.integer_.equals(x.integer_);
        }
        return false;
    }

    public int hashCode() {

        return 37 * (this.op_.hashCode()) + this.integer_.hashCode();
    }

}
