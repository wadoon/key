package de.uka.ilkd.key.testgeneration.parsers;

import java.util.LinkedList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;

/**
 * Children of this class represent parsers which can be used to in various ways process
 * {@link Term}s in the process of test case generation.
 * 
 * @author christopher
 */
public abstract class AbstractTermParser {

    protected final TermFactory termFactory = TermFactory.DEFAULT;

    /**
     * The names of the various primitive types in Java. As of the implementation of this class
     * (November 2012), KeY does not support floating point types (i.e. <b>float</b> and
     * <b>double</b>), and neither does KeYTestGen2.
     */
    protected static final LinkedList<String> primitiveTypes;

    /**
     * The sort names of the various binary functions represented in the KeY {@link Term} hierarchy.
     * Note that equality is not a part of this list, since it is represented by its own operational
     * type {@link Equality}.
     */
    protected static final LinkedList<String> binaryFunctions;
    static {

        primitiveTypes = new LinkedList<String>();
        primitiveTypes.add("byte");
        primitiveTypes.add("int");
        primitiveTypes.add("long");
        primitiveTypes.add("boolean");

        binaryFunctions = new LinkedList<String>();

        // The Greater-Or-Equals (>=) operator
        binaryFunctions.add("geq");
        // The Less-Or-Equals (<=) operator
        binaryFunctions.add("leq");
        // The multiplication (*) operator
        binaryFunctions.add("mul");
        // The division (/) operator
        binaryFunctions.add("div");
        // The addition (+) operator
        binaryFunctions.add("add");
        // The subtraction (-) operator
        binaryFunctions.add("sub");
    }

    /**
     * Constructs a new binary {@link Junctor} depending on the kind of Junctor represented by the
     * input {@link Term}.
     * 
     * @param term
     *            the original Term
     * @param firstChild
     *            first subterm of the original Term
     * @param secondChild
     *            second subterm of the original Term
     * @return
     * @throws ModelGeneratorException
     */
    protected Term createBinaryJunctor(Term term, Term firstChild, Term secondChild)
            throws ModelGeneratorException {

        String junctorName = term.op().name().toString();

        if (junctorName.equals("and")) {
            return termFactory.createTerm(Junctor.AND, firstChild, secondChild);
        }

        if (junctorName.equals("or")) {
            return termFactory.createTerm(Junctor.OR, firstChild, secondChild);
        }

        if (junctorName.equals("equals")) {
            return termFactory.createTerm(term.op(), firstChild, secondChild);
        }

        throw new ModelGeneratorException("Parse error");
    }

    /**
     * Extracts the name of a field, given a representation on the form:
     * <code>[package].[class]::$[field]</code>
     * 
     * @param string
     * @return
     */
    protected String extractName(Term term) {

        String fullName = term.toString();
        int splitterIndex = fullName.lastIndexOf('$');

        if (splitterIndex == -1) {
            return term.toString();
        }

        return fullName.substring(splitterIndex + 1).replaceAll("[^A-Za-z0-9]", "");
    }
}
