package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.FreeLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;

/** Generic data type, which has no predefined theory.
 * It is meant as a basis to implement an additional abstract data type,
 * e.g., binary trees, stacks, etc. in <code>.key</code> files.
 * @author daniel
 *
 */
public final class FreeLDT extends LDT {

    public static final Name NAME = new Name("Free");
    
    // neutral element, the only pre-defined function
    private Function atom;

    public FreeLDT(IServices services) {
        super(NAME, services);
        atom      = addFunction(services, "atom");
    }


    @Override
    public boolean isResponsible(Operator op, Term[] subs, IServices services, ExecutionContext ec) {
        return false;  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right,
            IServices services, ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, IServices services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, IServices services) {
        return services.getTermBuilder().func(atom);
    }

    @Override
    public Function getFunctionFor(Operator op, IServices services,
            ExecutionContext ec) {
        // TODO Auto-generated method stub
        assert false;
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return "atom".equals(f.name().toString());
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, IServices services) {
        if(t.op() instanceof Function && hasLiteralFunction((Function)t.op())) {
            return FreeLiteral.INSTANCE;
        }
        assert false;
        return null;
    }

    @Override
    public Type getType(Term t) {
        assert false;
        return null;
    }
    
    public Function getAtom(){
        return atom;
    }

}
