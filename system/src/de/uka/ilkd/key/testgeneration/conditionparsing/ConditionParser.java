package de.uka.ilkd.key.testgeneration.conditionparsing;

import java.util.LinkedList;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.implementation.IModelVariable;
import de.uka.ilkd.key.testgeneration.model.modelgeneration.implementation.ModelVariable;

/**
 * Encapsulates various methods aimed at parsing a pathcondition ({@link Term})
 * for the purpose of test case generation
 * 
 * @author christopher
 */
public class ConditionParser {

    private final TermFactory termFactory = TermFactory.DEFAULT;

    private static final LinkedList<String> primitiveTypes;
    private static final LinkedList<String> binaryFunctions;
    static {

        primitiveTypes = new LinkedList<String>();
        primitiveTypes.add("int");

        binaryFunctions = new LinkedList<String>();
        binaryFunctions.add("geq");
        binaryFunctions.add("leq");
        binaryFunctions.add("mul");
        binaryFunctions.add("div");
        binaryFunctions.add("add");
        binaryFunctions.add("sub");
    }

    /**
     * Given an initial {@link Term}, constructs a simpler Term which
     * "localizes" all occurences of primitive datatypes, by transforming the
     * instances of {@link SortDependingFunction} which contain them.
     * <p>
     * As an example of how this works, consider the case where we have an
     * instace of some class <code>Base</code> named "base", which as a field
     * has an instance of some other class <code>Inner</code> named "inner",
     * which in turn has a local instance of an <code>integer </code> named
     * "localInt. Normally, simply transforming such a construct to an SMT-LIB
     * formula would result in a needlesly complex expression and model, which
     * is a waste of both resources and time invested in developing additional
     * parsers to understand it.
     * <p>
     * What we do instead is to simply transform the construct into a local
     * variable of our base class, giving it a name corresponding to its nesting
     * order. In our case, such a name migh be "base$nested$localInt". When all
     * variables have been processed like this, we end up with a greatly
     * simplified term which can easily be expressed as an SMT-LIB construct.
     * <p>
     * This process will also remove all implied properties of internal objects,
     * such as not-null requirements, since these are not needed in the
     * simplified formula, and would only further pollute the SMT-LIB
     * expression. Further, it will simplify the formula by removing unnecessary
     * conjuntions.
     * 
     * @param term
     *            the term to process
     * @return the simplified term
     * @throws ModelGeneratorException
     */
    public Term simplifyTerm(Term term) throws ModelGeneratorException {

        Operator operator = term.op();

        if (operator instanceof Function) {
            return simplifyFunction(term);
        }

        if (operator instanceof Equality) {
            return simplifyEquals(term);
        }

        if (operator instanceof Junctor) {
            return simplifyJunctor(term);
        }

        for (int i = 0; i < term.arity(); i++) {
            simplifyTerm(term.sub(i));
        }

        return term;
    }

    /**
     * In terms of logical representation, equality differs from the other
     * comparators (leq, geq etc) in the sense that it can be applied to boolean
     * values as well as numeric ones. Thus, it is treated differently in the
     * sense that we simplify it the same way that we simplify junctors.
     * 
     * @param term
     * @return
     * @throws ModelGeneratorException
     */
    private Term simplifyEquals(Term term) throws ModelGeneratorException {

        return simplifyJunctor(term);
    }

    private Term simplifyFunction(Term term) throws ModelGeneratorException {

        Operator operator = term.op();

        if (operator.toString().equals("null")) {
            return null;
        }

        if (operator instanceof SortDependingFunction) {
            return simplifySortDependentFunction(term);
        }

        if (binaryFunctions.contains(operator.toString())) {
            return simplifyBinaryFunction(term);
        }

        return term;
    }

    private Term simplifyBinaryFunction(Term term)
            throws ModelGeneratorException {

        // Function function = new Function(term.op().name(), term.sort());
        Term firstChild = simplifyTerm(term.sub(0));
        Term secondChild = simplifyTerm(term.sub(1));

        Term newTerm =
                termFactory.createTerm(term.op(), firstChild, secondChild);

        return newTerm;
    }

    /**
     * Given an {@link Term} of type {@link SortDependingFunction}, with a
     * primitive type as its sort, resolve the nesting hierarchy for this
     * variable, and encode this information as a new local variable, whose name
     * will depend on the classes involved in the nesting hierarchy. For
     * example, the int value x in the hiearchy main.nested.other.yetanother.x
     * will be renamed "main$nested$other$yetanother$x", and treated simply as a
     * local variable in the object main.
     * 
     * @param term
     *            the term to process
     * @return a Term representing the nested variable as a local variable
     */
    private Term simplifySortDependentFunction(Term term) {

        String sortName = term.sort().toString();

        /*
         * Check if the base type of the selection statement is a primitive type
         * (we do not handle anything else). If so, create an alias for the
         * nested variable, and return everything else as a new
         * LocationVariable.
         */
        if (primitiveTypes.contains(sortName)) {

            ProgramElementName resolvedVariableName =
                    new ProgramElementName(simplifySortDependentFunctionHelper(term));

            LocationVariable resolvedVariable =
                    new LocationVariable(resolvedVariableName, term.sort());

            return termFactory.createTerm(resolvedVariable);
        }

        return null;
    }

    private String simplifySortDependentFunctionHelper(Term term) {

        /*
         * Base case: underlying definition does not consist of any more nested
         * recursions, so we just extract the current variable name and go back.
         */
        if (term.op().getClass() == LocationVariable.class) {

            return extractName(term);
        }

        /*
         * Recursive case: underlying definition is still recursively defined,
         * so keep unwinding it.
         */
        else {

            return simplifySortDependentFunctionHelper(term.sub(1)) + "$"
                    + extractName(term);
        }
    }

    /**
     * Simplify a junctor (i.e. NOT, AND, OR, IMP).
     * 
     * @param term
     *            the term to simplify
     * @return the simplified term
     * @throws ModelGeneratorException
     */
    private Term simplifyJunctor(Term term) throws ModelGeneratorException {

        String junctorName = term.op().toString();

        if (junctorName.equals("and"))
            return simplifyBinaryJunctor(term);
        if (junctorName.equals("or"))
            return simplifyBinaryJunctor(term);
        if (junctorName.equals("equals"))
            return simplifyBinaryJunctor(term);
        if (junctorName.equals("not"))
            return simplifyNot(term);

        throw new ModelGeneratorException("Parse error");
    }

    /**
     * Simplify a negation. If the child is simplified to null, simply return
     * null. Otherwise, create a new negation of the simplification of the
     * child.
     * 
     * @param term
     *            the term (logical negator) to simplify
     * @return the simplified negation
     * @throws ModelGeneratorException
     */
    private Term simplifyNot(Term term) throws ModelGeneratorException {

        Term newChild = simplifyTerm(term.sub(0));

        if (newChild == null) {
            return null;
        }

        return termFactory.createTerm(Junctor.NOT, newChild);
    }

    /**
     * Simplifies a binary junctor by examining the operands. If one of them can
     * be simplified to null, the entire junction can be replaced by the second
     * operand. If both are simplified to null, the entire conjunction can be
     * removed (hence this method will return null as well).
     * 
     * @param term
     * @throws ModelGeneratorException
     */
    private Term simplifyBinaryJunctor(Term term)
            throws ModelGeneratorException {

        Term firstChild = simplifyTerm(term.sub(0));
        Term secondChild = simplifyTerm(term.sub(1));

        if (firstChild != null && secondChild == null) {
            return firstChild;
        }
        if (firstChild == null && secondChild != null) {
            return secondChild;
        }
        if (firstChild != null && secondChild != null) {
            return createBinaryJunctor(term, firstChild, secondChild);
        }

        return null;
    }

    /**
     * Constructs a new binary {@link Junctor} depending on the kind of Junctor
     * represented by the input {@link Term}.
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
    private Term createBinaryJunctor(
            Term term,
            Term firstChild,
            Term secondChild) throws ModelGeneratorException {

        String junctorName = term.op().name().toString();

        if (junctorName.equals("and"))
            return termFactory.createTerm(Junctor.AND, firstChild, secondChild);

        if (junctorName.equals("or"))
            return termFactory.createTerm(Junctor.OR, firstChild, secondChild);

        if (junctorName.equals("equals"))
            return termFactory.createTerm(term.op(), firstChild, secondChild);

        throw new ModelGeneratorException("Parse error");
    }

    /**
     * Extracts the name of a field, given a representation on the form:
     * <code>[package].[class]::$[field]</code>
     * 
     * @param string
     * @return
     */
    private String extractName(Term term) {

        String fullName = term.toString();
        int splitterIndex = fullName.lastIndexOf('$');

        if (splitterIndex == -1) {
            return term.toString();
        }

        return fullName.substring(splitterIndex + 1).replaceAll(
                "[^A-Za-z0-9]", "");
    }
}
