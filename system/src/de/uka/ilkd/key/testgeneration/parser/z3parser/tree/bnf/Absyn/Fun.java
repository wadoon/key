package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public abstract class Fun
        implements java.io.Serializable {

    public abstract <R, A> R accept(Fun.Visitor<R, A> v, A arg);

    public interface Visitor<R, A> {

        public R visit(
                de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.Function p,
                A arg);

    }

}
