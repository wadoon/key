package edu.kit.iti.formal.psdbg.interpreter.data;

import edu.kit.iti.formal.psdbg.parser.ast.Variable;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.Setter;
import lombok.ToString;

import javax.annotation.Nonnull;

/**
 * Objects of this class represent a GoalNode in a script state
 * If parent is null, this is the root
 *
 * @author S.Grebing
 */
@ToString(of = "id")
@EqualsAndHashCode(of = "id")
public class GoalNode<T> {
    @Getter
    @Setter
    private VariableAssignment assignments;

    @Getter
    private GoalNode<T> parent;

    @Getter
    private T data;

    @Getter
    private boolean isClosed;

    private int id = super.hashCode();

    public GoalNode(T data) {
        this(null, new VariableAssignment(), data, false);
    }

    public GoalNode(@Nonnull GoalNode<T> parent, T data, boolean isClosed) {
        this(parent, parent.getAssignments(), data, isClosed);
    }

    private GoalNode(@Nonnull GoalNode<T> parent, VariableAssignment assignments, T data, boolean isClosed) {
        this.assignments = assignments.push();
        this.parent = parent;
        this.data = data;
        this.isClosed = isClosed;
    }

    private GoalNode(int id, GoalNode<T> parent, T data, boolean isClosed) {
        this(parent, data, isClosed);
        this.id = id;
    }

    private GoalNode(int id, T data, boolean isClosed) {
        this(data);
        this.isClosed = isClosed;
        this.id = id;
    }

    /**
     * @param varname
     * @return value of variable if it exists
     */
    public Value getVariableValue(Variable varname) {
        return assignments.getValue(varname);

    }

    /**
     * Lookup the type of the variable in the type map
     *
     * @param varname
     * @return
     */
    public Type getVariableType(Variable varname) {
        Type t = this.getAssignments().getType(varname);
        if (t == null) {
            throw new RuntimeException("Variable " + varname + " must be declared first");
        } else {

            return t;
        }
    }


    /**
     * Add a variable declaration to the type map (TODO Default value in map?)
     *
     * @param name
     * @param type
     * @throws NullPointerException
     */
    public void declareVariable(Variable name, Type type) {
        this.getAssignments().declare(name, type);
    }

    /**
     * Set the value of a variable in the value map
     *
     * @param name
     * @param value
     */
    public void setVariableValue(Variable name, Value value) {
        getAssignments().assign(name, value);
    }

    /**
     * Enter new variable scope and push onto stack
     */
    public VariableAssignment enterScope() {
        assignments = assignments.push();
        return assignments;
    }


    public VariableAssignment exitScope() {
        this.assignments = this.assignments.pop();
        return assignments;
    }

    /**
     * @deprecated weigl: IMHO this method creates a lot of pain in analyses of goal nodes dependency.
     * For example we can't guarant gn.getParent() == gn' for checking inheritance.
     * Currently solved by id field.
     * @return
     */
    public GoalNode<T> deepCopy() {
        if (parent != null) {
            return new GoalNode<T>(id, parent.deepCopy(), data, isClosed);
        } else {
            return new GoalNode<T>(id, data, isClosed);
        }
    }

    public VariableAssignment enterScope(VariableAssignment va) {
        assignments = assignments.push(va);
        return assignments;
    }


}
