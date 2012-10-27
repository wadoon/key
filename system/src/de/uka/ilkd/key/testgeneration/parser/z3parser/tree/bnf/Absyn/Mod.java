package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public class Mod
        extends Modl {

    public final ListFun listfun_;

    public Mod(ListFun p1) {

        listfun_ = p1;
    }

    public <R, A> R accept(
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Modl.Visitor<R, A> v,
            A arg) {

        return v.visit(this, arg);
    }

    public boolean equals(Object o) {

        if (this == o)
            return true;
        if (o instanceof de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Mod) {
            de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Mod x =
                    (de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Mod) o;
            return this.listfun_.equals(x.listfun_);
        }
        return false;
    }

    public int hashCode() {

        return this.listfun_.hashCode();
    }

}
