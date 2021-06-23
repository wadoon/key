package keyext.extract_preconditions.projections.visitors;

import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import java.util.HashSet;
import java.util.Set;

/**
 * Visitor which collects all visited ProgramVariables
 */
class FindVarNamesVisitor extends DefaultVisitor {

    /**
     * The set of all found variables
     */
    private final Set<Name> foundVariables;

    /**
     * Constructor for a FindVarNamesVisitor.
     */
    public FindVarNamesVisitor() {
        foundVariables = new HashSet<>();
    }

    /**
     * Returns all collected ProgramVariables
     * Must only be called after visiting terms
     *
     * @return A set of all collected variables.
     */
    public Set<Name> getVariables() {
        return foundVariables;
    }

    @Override
    public boolean visitSubtree(Term visited) {
        if (visited.op() instanceof Function){
            if (isSelectTerm(visited) ||
                isStoreTerm(visited) ||
                visited.op().name().toString().endsWith("<inv>")) {
                // We enter select/store functions manually...
                // Also we ignore <inv> for now
                // TODO(steuber): Is it OK to ignore inv?
                return false;
            }
        }
        return true;
    }

    @Override
    public void visit(Term visited) {
        if (isBuiltinObjectProperty(visited)) {
            // We are not interested in those (right?)
            return;
        }
        if (visited.op() instanceof ProgramVariable) {
            ProgramVariable var = (ProgramVariable) visited.op();
            this.foundVariables.add(var.name());
        }
        if (visited.op() instanceof Function) {
            Function fun = (Function) visited.op();
            Name funName = visited.op().name();
            if (fun.sort().name().toString().equals("Field")) {
                this.foundVariables.add(funName);
            } else if (isSelectTerm(visited)){
                visited.sub(2).execPostOrder(this);
            } else if (isStoreTerm(visited)) {
                visited.sub(2).execPostOrder(this);
                visited.sub(3).execPostOrder(this);
            }
        }
    }

    /**
     * Returns whether the given term is a select statement.
     *
     * Based on implementation in ExpressionBuilder
     */
    private static boolean isSelectTerm(Term term) {
        return term.op().name().toString().endsWith("::select") && term.arity() == 3;
    }

    private static boolean isStoreTerm(Term term) {
        return term.op().name().toString().endsWith("store") && term.arity() == 4;
    }

    // Adopted from FieldPrinter.java
    protected boolean isBuiltinObjectProperty(Term fieldTerm) {
        return fieldTerm.op().name().toString().contains("::<")
            && isFieldConstant(fieldTerm);
    }
    protected static boolean isFieldConstant(Term fieldTerm) {
        return fieldTerm.op() instanceof Function
            && ((Function) fieldTerm.op()).isUnique()
            && fieldTerm.sort().name().toString().equals("Field")
            && fieldTerm.arity() == 0
            && fieldTerm.boundVars().isEmpty();
    }
}
