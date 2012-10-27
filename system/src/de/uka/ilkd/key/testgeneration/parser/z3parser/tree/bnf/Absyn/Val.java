package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public abstract class Val
        implements java.io.Serializable {

    public abstract <R, A> R accept(Val.Visitor<R, A> v, A arg);

    public interface Visitor<R, A> {

        public R visit(
                de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.EVal p,
                A arg);

        public R visit(
                de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.ENVal p,
                A arg);

    }

}
