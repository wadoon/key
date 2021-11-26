package org.key_project.java;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import static org.key_project.java.JavaSorts.JAVA_STATEMENT;

public class JavaOperator implements Operator {
    private final Sort[] expectedSorts;
    private final int bindVarsAt;
    private final boolean rigid;
    private final Name name;

    public JavaOperator(String name, Sort[] expected, int bindVarsAt, boolean rigid) {
        this.name = new Name("java" + name);
        this.rigid = rigid;
        this.bindVarsAt = bindVarsAt;
        expectedSorts = expected;
    }

    public JavaOperator(String name, Sort... expectedSorts) {
        this(name, expectedSorts, -1, false);
    }

    @Override
    public int arity() {
        return expectedSorts.length;
    }


    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        return JAVA_STATEMENT;
    }

    @Override
    public boolean bindVarsAt(int n) {
        if (bindVarsAt < 0) {
            return false;
        }
        return n >= bindVarsAt;
    }

    @Override
    public boolean isRigid() {
        return rigid;
    }

    @Override
    public void validTopLevelException(Term term) throws TermCreationException {

    }

    @Override
    public boolean validTopLevel(Term term) {
        return true;
    }

    @Override
    public Name name() {
        return name;
    }
}
