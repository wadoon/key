package de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn; // Java
                                                                       // Package
                                                                       // generated
                                                                       // by the
                                                                       // BNF
                                                                       // Converter.

public abstract class Op
        implements java.io.Serializable {

    public abstract <R, A> R accept(Op.Visitor<R, A> v, A arg);

    public interface Visitor<R, A> {

        public R visit(
                de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.SNeg p,
                A arg);

        public R visit(
                de.uka.ilkd.key.testgeneration.parser.z3parser.tree.bnf.Absyn.SPos p,
                A arg);

    }

}
