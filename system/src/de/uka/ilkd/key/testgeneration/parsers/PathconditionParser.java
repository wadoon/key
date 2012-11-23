package de.uka.ilkd.key.testgeneration.parsers;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelInstance;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.visitors.KeYTestGenTermVisitor;

/**
 * Provides various methods for processing the pathconditions for {@link IExecutionNode} instances.
 * 
 * @author christopher
 */
public class PathconditionParser
        extends AbstractTermParser {

    /**
     * Allow only static access
     */
    private PathconditionParser() {

    }

    /**
     * Creates a skeletal {@link Model} instance from a {@link Term}. The Term will be parsed, and
     * all representations of program variables (along with their relationships to one another) will
     * be used to construct a "skeletal" Model instance (i.e. no concrete primitive values).
     * 
     * @param term
     *            the Term to process
     * @param services
     *            {@link Services} associated with the Term
     * @return the Model instance built from the Term
     */
    public static Model createModel(Term term, Services services) {

        TermModelVisitor modelVisitor = new TermModelVisitor(services);
        term.execPreOrder(modelVisitor);

        return modelVisitor.getModel();
    }

    /**
     * Given an initial {@link Term}, constructs a simpler Term which "localizes" all occurences of
     * primitive datatypes, by transforming the instances of {@link SortDependingFunction} which
     * contain them.
     * <p>
     * As an example of how this works, consider the case where we have an instace of some class
     * <code>Base</code> named "base", which as a field has an instance of some other class
     * <code>Inner</code> named "inner", which in turn has a local instance of an
     * <code>integer </code> named "localInt. Normally, simply transforming such a construct to an
     * SMT-LIB formula would result in a needlesly complex expression and model, which is a waste of
     * both resources and time invested in developing additional parsers to understand it.
     * <p>
     * What we do instead is to simply transform the construct into a local variable of our base
     * class, giving it a name corresponding to its nesting order. In our case, such a name migh be
     * "base$nested$localInt". When all variables have been processed like this, we end up with a
     * greatly simplified term which can easily be expressed as an SMT-LIB construct.
     * <p>
     * This process will also remove all implied properties of internal objects, such as not-null
     * requirements, since these are not needed in the simplified formula, and would only further
     * pollute the SMT-LIB expression. Further, it will simplify the formula by removing unnecessary
     * conjuntions.
     * 
     * @param term
     *            the term to process
     * @return the simplified term
     * @throws ModelGeneratorException
     */
    public static Term simplifyTerm(Term term) throws ModelGeneratorException {

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
     * In terms of logical representation, equality differs from the other comparators (leq, geq
     * etc) in the sense that it can be applied to boolean values as well as numeric ones. Thus, it
     * is treated differently in the sense that we simplify it the same way that we simplify
     * junctors.
     * 
     * @param term
     * @return
     * @throws ModelGeneratorException
     */
    private static Term simplifyEquals(Term term) throws ModelGeneratorException {

        return simplifyJunctor(term);
    }

    /**
     * Simplifies a {@link Function} instance
     * 
     * @param term
     * @return
     * @throws ModelGeneratorException
     */
    private static Term simplifyFunction(Term term) throws ModelGeneratorException {

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

    /**
     * Simplifies a binary function (i.e. any instance of {@link Function} taking two operands, such
     * as the comparators).
     * 
     * @param term
     * @return
     * @throws ModelGeneratorException
     */
    private static Term simplifyBinaryFunction(Term term) throws ModelGeneratorException {

        // Function function = new Function(term.op().name(), term.sort());
        Term firstChild = simplifyTerm(term.sub(0));
        Term secondChild = simplifyTerm(term.sub(1));

        Term newTerm = termFactory.createTerm(term.op(), firstChild, secondChild);

        return newTerm;
    }

    /**
     * Given an {@link Term} of type {@link SortDependingFunction}, with a primitive type as its
     * sort, resolve the nesting hierarchy for this variable, and encode this information as a new
     * local variable, whose name will depend on the classes involved in the nesting hierarchy. For
     * example, the int value x in the hiearchy main.nested.other.yetanother.x will be renamed
     * "main$nested$other$yetanother$x", and treated simply as a local variable in the object main.
     * 
     * @param term
     *            the term to process
     * @return a Term representing the nested variable as a local variable
     */
    private static Term simplifySortDependentFunction(Term term) {

        String sortName = term.sort().toString();

        /*
         * Check if the base type of the selection statement is a primitive type (we do not handle
         * anything else). If so, create an alias for the nested variable, and return everything
         * else as a new LocationVariable.
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

    /**
     * Recursive helper method to {@link #simplifyBinaryFunction(Term)}
     * 
     * @param term
     *            the Term to process
     * @return a String representation of a variable path
     */
    private static String simplifySortDependentFunctionHelper(Term term) {

        /*
         * Base case: underlying definition does not consist of any more nested recursions, so we
         * just extract the current variable name and go back.
         */
        if (term.op().getClass() == LocationVariable.class) {

            return extractName(term);
        }

        /*
         * Recursive case: underlying definition is still recursively defined, so keep unwinding it.
         */
        else {

            return simplifySortDependentFunctionHelper(term.sub(1)) + "_dot_"
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
    private static Term simplifyJunctor(Term term) throws ModelGeneratorException {

        String junctorName = term.op().toString();

        if (junctorName.equals("and")) {
            return simplifyBinaryJunctor(term);
        }
        else if (junctorName.equals("or")) {
            return simplifyBinaryJunctor(term);
        }
        else if (junctorName.equals("equals")) {
            return simplifyBinaryJunctor(term);
        }
        else if (junctorName.equals("not")) {
            return simplifyNot(term);
        }
        else {
            throw new ModelGeneratorException("Parse error");
        }
    }

    /**
     * Simplify a negation. If the child is simplified to null, simply return null. Otherwise,
     * create a new negation of the simplification of the child.
     * 
     * @param term
     *            the term (logical negator) to simplify
     * @return the simplified negation
     * @throws ModelGeneratorException
     */
    private static Term simplifyNot(Term term) throws ModelGeneratorException {

        Term newChild = simplifyTerm(term.sub(0));

        if (newChild == null) {
            return null;
        }

        return termFactory.createTerm(Junctor.NOT, newChild);
    }

    /**
     * Simplifies a binary junctor by examining the operands. If one of them can be simplified to
     * null, the entire junction can be replaced by the second operand. If both are simplified to
     * null, the entire conjunction can be removed (hence this method will return null as well).
     * 
     * @param term
     * @throws ModelGeneratorException
     */
    private static Term simplifyBinaryJunctor(Term term) throws ModelGeneratorException {

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
    private static Term createBinaryJunctor(Term term, Term firstChild, Term secondChild)
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
     * This Visitor walks a {@link Term} and extracts information related to the program variables
     * represented in the term. The goal of this procedure is to provide sufficient information for
     * later constructing a {@link Model} including the extracted variables.
     * 
     * @author christopher
     */
    private static class TermModelVisitor
            extends Visitor {

        /**
         * Returns the model generated by the visitationprocess
         * 
         * @return
         */
        public Model getModel() {

            return model;
        }

        /**
         * Stores Java specific information related to the {@link Term} we are working with.
         */
        private final JavaInfo javaInfo;

        /**
         * The default root variable, representing a reference to the class instance of which the
         * tested method is part.
         */
        private static final LocationVariable default_self =
                new LocationVariable(new ProgramElementName("$SELF$"), new KeYJavaType());

        /**
         * Flag to indicate if we have seen a Not operator.
         */
        private boolean sawNot;

        /**
         * The {@link Model} instance generated by this visitor instance.
         */
        Model model = new Model();

        public TermModelVisitor(Services services) {

            javaInfo = services.getJavaInfo();

            /*
             * Add the root variable and instance to the Model
             */
            ModelInstance selfInstance = new ModelInstance(default_self.getKeYJavaType());
            ModelVariable self = new ModelVariable(default_self, "self", selfInstance);
            model.add(self, selfInstance);
        }

        /**
         * Visit a {@link Term} node, extracting any data related to {@link ProgramVariable}
         * instances in this node, if any. If such data is found, it will be encoded in a
         * {@link ModelVariable} format.
         * <p>
         * <strong>IMPORTANT:</strong> Due to how {@link Term} ASTs are implemented, this method
         * will only have the desired effect if the visitation is carried out in postorder. Preorder
         * will cause the Model to be constructed with wrong parent-child relationships.
         * <p>
         * To achieve correct results, thus, please only pass this visitor as a parameter to
         * {@link Term#execPostOrder(de.uka.ilkd.key.logic.Visitor)}
         * <p>
         * TODO: This entire class should be re-implemented as a one-way parser. See
         * {@link PathconditionParser}.
         */
        @Override
        public void visit(Term visited) {

            Operator operator = visited.op();

            if (isVariable(visited)) {
                parseVariableTerm(visited);
            }
            else if (operator instanceof Junctor && operator.toString().equals("not")) {
                sawNot = true;
            }
            else if (operator instanceof Equality && !sawNot) {
                parseEquals(visited);
                sawNot = false;
            }
            else if (operator instanceof Junctor) {
                sawNot = false;
            }
        }

        /**
         * Parse a {@link Term} representing a program variable. Such a Term can be either a plain
         * local declaration (i.e. a {@link LocationVariable}), or it can be part of a nested
         * hierarchy (i.e. a {@link SortDependingFunction}). We treat both cases here.
         * 
         * @param term
         *            the term to parse
         */
        private void parseVariableTerm(Term term) {

            /*
             * If the program variable instance resolves to null, it does not correspond to a
             * variable type recognized by KeYTestGen (this is likely to change in the future).
             * 
             * Also, if the variable corresponds to the root type, we do not process it (since it is
             * already part of the model by default.
             * 
             * FIXME: There must be a cleaner way of checking if the root variable has been found -
             * this is a terribly ugly hack. Check if sort is null instead? What other variables (if
             * any) may have nulled sorts?
             */
            ProgramVariable programVariable = getVariable(term);
            if (programVariable == null || programVariable.toString().equals("$SELF$")) {
                return;
            }

            /*
             * Create the variable itself, together with its corresponding instance. If the variable
             * is a primitive type, a corresponding wrapper class has to be generated in order to
             * represent its value. If it is not primitive, we simply create a new ModelInstance to
             * hold any reference object.
             */
            String identifier = resolveIdentifierString(term);
            ModelVariable variable = new ModelVariable(programVariable, identifier);

            Object instance = null;
            if (isPrimitiveType(term)) {
                instance = resolvePrimitiveType(programVariable);
            }
            else {
                instance = new ModelInstance(programVariable.getKeYJavaType());
            }

            /*
             * Add the variable and its instance to the Model. This might seem premature, but must
             * be done to preserve referential integrity and avoiding extra work.
             */
            model.add(variable, instance);

            /*
             * If the term is a SortDependingFunction, we are faced with two possibilities:
             * 
             * 1. the variable in question may be a field of some instance. In this case, we attempt
             * to resolve the variable pointing to this instance, in order to add the our newly
             * created variable as a field of that instance.
             * 
             * 2. the variable is null, in which case this variable must be a static field of its
             * declaring class. In this case, it is not part of any instance, and we let the parent
             * remain null.
             */
            if (term.op().getClass() == SortDependingFunction.class) {

                ProgramVariable parentVariable = getVariable(term.sub(1));

                /*
                 * The parent is not null, and this variable is hence an instance variable of some
                 * class. Connect it to the parent.
                 */
                if (parentVariable != null) {
                    String parentIdentifier = resolveIdentifierString(term.sub(1));
                    ModelVariable parentModelVariable =
                            new ModelVariable(parentVariable, parentIdentifier);

                    model.assignField(variable, parentModelVariable);
                }
                else if (!programVariable.isStatic()) {

                    ModelVariable self = new ModelVariable(default_self, "self");
                    model.assignField(variable, self);
                }
            }

            /*
             * Finally, if the variable was not a SortDependentFunction (i.e. did not have an
             * explicitly declared parent), we deduce that it is a locally declared variable, and
             * hence set its parent to be the root class.
             */
            else {
                ModelVariable self = new ModelVariable(default_self, "self");
                model.assignField(variable, self);
            }
        }

        /**
         * Equality has to be dealt with depending on the type of the <strong>left-hand</strong>
         * variable, since this is the operand which will determine the meaning of the equality.
         * <p>
         * If the variable is <strong>primitve</strong>, equality, in our abstraction, implies a
         * value assignment: equals(a,b) simply means that the value of b is copied into a. There is
         * no need to do this explicitly here, since the SMT interface will taking care of this, and
         * we would thus only be performing the same work twice.
         * <p>
         * If the variable is a <strong>reference</strong> type, things get more interesting, since
         * equality in this case implies that the operands are pointing to a common object in
         * memory. To represent this in our abstraction, we need to cross-reference to Value
         * property of both operands, making them point to each other. We do this by making sure
         * that whatever Value is assigned to both operands has the same unique identifier.
         * 
         * @param term
         *            the term to process
         */
        private void parseEquals(Term term) {

            Term leftOperand = term.sub(0);
            Term rightOperand = term.sub(1);

            /*
             * The left-hand operator is a reference type
             */
            if (!isPrimitiveType(term)) {

                String leftOperandIdentifier = resolveIdentifierString(leftOperand);
                String rightOperandIdentifier = resolveIdentifierString(rightOperand);

                ModelVariable leftModelVariable =
                        model.getVariableByReference(leftOperandIdentifier);

                ModelVariable rightModelVariable =
                        model.getVariableByReference(rightOperandIdentifier);

                model.assignPointer(leftModelVariable, rightModelVariable);
            }
        }

        /**
         * Retrieve the {@link ProgramVariable} represented by a given {@link Term}, if any.
         * 
         * @param term
         *            the term to process
         * @return the {@link ProgramVariable} corresponding to the Term, iff. the Term represents a
         *         variable.
         */
        private ProgramVariable getVariable(Term term) {

            Operator operator = term.op();

            /*
             * Process an instance of ProgramVariable (most often, this will be a LocationVariable).
             * Such an object will represent a non-static field of some class, and its parent is as
             * such simply an instance of that class.
             */
            if (operator instanceof ProgramVariable) {

                /*
                 * Key represents the heap as a LocationVariable as well. We cannot(?) do anything
                 * useful with it, so we ignore it. However, if the LocationVariable correspons to
                 * "self" (i.e. the root variable), we return the default root, although we first
                 * properly set the type (which is not needed, but nice to have).
                 */
                if (!operator.toString().equalsIgnoreCase("heap")) {

                    if (operator.toString().equalsIgnoreCase("self")) {

                        ProgramVariable variable = (ProgramVariable) operator;
                        Type realType = variable.getKeYJavaType().getJavaType();
                        default_self.getKeYJavaType().setJavaType(realType);

                        return default_self;
                    }
                    else {
                        return (ProgramVariable) operator;
                    }
                }
            }

            /*
             * Process a normal Function. This step is necessary since the root instance of the
             * class holding the method under test (i.e. "self") will be of this type. If self is
             * encountered, insert a placebo variable for it (since KeY does not always create a
             * native variable for it).
             */
            if (operator.getClass() == Function.class) {

                if (operator.toString().equalsIgnoreCase("self")) {

                    ProgramVariable variable = (ProgramVariable) operator;
                    Type realType = variable.getKeYJavaType().getJavaType();
                    default_self.getKeYJavaType().setJavaType(realType);

                    return default_self;
                }
            }

            /*
             * Process a SortDependingFunction. A Term of this sort represents a recursively defined
             * variable (i.e. a variable at the end of a nested hiearchy, such as
             * self.nestedObject.anotherNestedObject.variable).
             */
            if (operator.getClass() == SortDependingFunction.class) {

                return getProgramVariableForField(term.sub(2));
            }
            return null;
        }

        /**
         * Works around the fact that KeY inserts the "$" sign into {@link Term}s, which messes with
         * the variable lookup of the {@link JavaInfo} instance.
         * 
         * @param term
         *            a {@link Term} with a sort of type Field
         * @return the {@link ProgramVariable} instance corresponding to the field represented by
         *         the Term
         */
        private ProgramVariable getProgramVariableForField(Term term) {

            if (!term.sort().name().toString().equalsIgnoreCase("Field")) {
                return null;
            }

            String[] split = term.op().toString().split("::\\$");
            return javaInfo.getAttribute(split[1], split[0]);
        }

        /**
         * Returns a wrapper representation of the primitive type of a variable
         * 
         * @param variable
         *            the variable
         * @return the primitive type of the variable
         */
        private Object resolvePrimitiveType(ProgramVariable variable) {

            /*
             * FIXME: Horrible. Do not do String comparison here, find a convenient way to compare
             * based on types.
             */
            String typeName = variable.getKeYJavaType().getFullName();
            if (typeName.equals("int")) {
                return new Integer(0);
            }
            if (typeName.equals("boolean")) {
                return new Boolean(false);
            }
            if (typeName.equals("long")) {
                return new Long(0L);
            }
            if (typeName.equals("byte")) {
                return new Boolean(false);
            }
            if (typeName.equals("char")) {
                return new Character('0');
            }
            else {
                return null;
            }
        }
    }
}