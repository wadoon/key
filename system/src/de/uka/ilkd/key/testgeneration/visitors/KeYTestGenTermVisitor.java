package de.uka.ilkd.key.testgeneration.visitors;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;

/**
 * Used to define a custom set of {@link Term} visitors used in KeYTestGen.
 * 
 * @author christopher
 */
public abstract class KeYTestGenTermVisitor
        extends Visitor {

    /**
     * Used for storing an index over all primitive types currently handled by KeYTestGen
     */
    protected static final LinkedList<String> primitiveTypes;

    /**
     * Used for storing an index of binary functions supported by KeYTestGen
     */
    protected static final LinkedList<String> binaryFunctions;

    static {

        primitiveTypes = new LinkedList<String>();
        primitiveTypes.add("int");
        primitiveTypes.add("boolean");
        primitiveTypes.add("long");
        primitiveTypes.add("byte");

        binaryFunctions = new LinkedList<String>();
        binaryFunctions.add("geq");
        binaryFunctions.add("leq");
        binaryFunctions.add("mul");
        binaryFunctions.add("div");
        binaryFunctions.add("add");
        binaryFunctions.add("sub");
    }

    /**
     * Check if the given term represents a program construct with a supported primitive type as its
     * base type, such as a method or local variable declaration.
     * 
     * @param term
     *            the term to check
     * @return true if the Term represents an integer program construct, false otherwise
     */
    protected boolean isPrimitiveType(Term term) {

        String sortName = term.sort().name().toString();

        return primitiveTypes.contains(sortName);
    }

    /**
     * Check if the given Term represents a binary function, such as any of the {@link Junctor}
     * instances.
     * 
     * @param term
     * @return
     */
    protected boolean isBinaryFunction(Term term) {

        de.uka.ilkd.key.logic.op.Operator operator = term.op();
        
        return operator instanceof Junctor || operator instanceof Equality;
    }
}
