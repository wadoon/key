package se.gu.svanefalk.testgeneration.core.model.implementation;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.visitors.KeYTestGenTermVisitor;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * This Visitor walks a {@link Term} and extracts information related to the
 * program variables represented in the term. The goal of this procedure is to
 * provide sufficient information for later constructing a {@link Model}
 * including the extracted variables.
 * 
 * @author christopher
 */
class TermToModelVisitor extends KeYTestGenTermVisitor {

    /**
     * Constant for separating fields in {@link SortDependingFunction}
     * instances.
     */
    private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR.toString();

    /**
     * Returns a wrapper representation of the primitive type of a variable
     * 
     * @param variable
     *            the variable
     * @return the primitive type of the variable
     */
    private static Object resolvePrimitiveType(final IProgramVariable variable) {

        /*
         * FIXME: Horrible. Do not do String comparison here, find a convenient
         * way to compare based on types.
         */
        final String typeName = variable.getKeYJavaType().getFullName();
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
            return new Byte("0xe0");
        }
        if (typeName.equals("char")) {
            return new Character('0');
        } else {
            return null;
        }
    }

    /**
     * The default root variable, representing a reference to the class instance
     * of which the tested method is part.
     */
    private final LocationVariable default_self;

    /**
     * Stores Java specific information related to the {@link Term} we are
     * working with.
     */
    private final JavaInfo javaInfo;

    /**
     * The {@link Model} to be populated by visiting the associated Term.
     */
    Model model;

    public TermToModelVisitor(final Model model, final IExecutionNode node) {

        final IExecutionMethodCall methodCall = getMethodCallNode(node);
        this.model = model;

        javaInfo = methodCall.getServices().getJavaInfo();

        /*
         * Construct the default base class.
         */
        final KeYJavaType container = methodCall.getProgramMethod().getContainerType();
        ProgramElementName elementName = new ProgramElementName("self");
        default_self = new LocationVariable(elementName, container);

        /*
         * Add the root variable and instance to the Model
         */
        final ModelInstance selfInstance = ModelInstance.constructModelInstance(container);

        final ModelVariable self = ModelVariable.constructModelVariable(
                default_self, "self");

        model.add(self, selfInstance);

        /*
         * Insert the method parameters by default. Their value do not matter at
         * this stage, as they will be instantiated later as needed.
         */
        final ImmutableArray<ParameterDeclaration> parameterDeclarations = methodCall.getProgramMethod().getParameters();

        for (final ParameterDeclaration parameterDeclaration : parameterDeclarations) {

            for (final VariableSpecification variableSpecification : parameterDeclaration.getVariables()) {

                /*
                 * Convert the declaration to a program variable
                 * 
                 * FIXME: I DO NOT WANT TO HAVE TO FLIPFLOP BETWEEN DIFFERENT
                 * ABSTRACTIONS!
                 */
                final KeYJavaType type = (KeYJavaType) variableSpecification.getType();

                final ProgramElementName name = new ProgramElementName(
                        variableSpecification.getName());

                final IProgramVariable programVariable = new LocationVariable(
                        name, type);

                final ModelVariable modelParameter = ModelVariable.constructModelVariable(
                        programVariable, name.toString());

                modelParameter.setParameter(true);

                /*
                 * The parameter is primitive.
                 */
                Object value = null;
                if (TermParserTools.isPrimitiveType(modelParameter.getTypeName())) {
                    value = TermToModelVisitor.resolvePrimitiveType(programVariable);
                } else {
                    value = ModelInstance.constructModelInstance(type);
                }
                model.add(modelParameter, value);
            }
        }
    }

    /**
     * Given an {@link IExecutionNode} somewhere in a symbolic execution tree
     * and below the method call node, backtracks until the method call node is
     * found.
     * 
     * @param node
     *            the node
     * @return
     */
    private IExecutionMethodCall getMethodCallNode(final IExecutionNode node) {

        if (node instanceof IExecutionMethodCall) {
            return (IExecutionMethodCall) node;
        } else {
            return getMethodCallNode(node.getParent());
        }
    }

    /**
     * Returns the model generated by the visitationprocess
     * 
     * @return
     */
    public Model getModel() {

        return model;
    }

    /**
     * Works around the fact that KeY inserts the "$" sign into {@link Term} s,
     * which messes with the variable lookup of the {@link JavaInfo} instance.
     * 
     * @param term
     *            a {@link Term} with a sort of type Field
     * @return the {@link ProgramVariable} instance corresponding to the field
     *         represented by the Term
     */
    private ProgramVariable getProgramVariableForField(final Term term) {

        if (!term.sort().name().toString().equalsIgnoreCase("Field")) {
            return null;
        }

        final String[] split = term.op().toString().split("::\\$");
        return javaInfo.getAttribute(split[1], split[0]);
    }

    /**
     * Retrieve the {@link ProgramVariable} represented by a given {@link Term},
     * if any.
     * 
     * @param term
     *            the term to process
     * @return the {@link ProgramVariable} corresponding to the Term, iff. the
     *         Term represents a variable.
     */
    private ProgramVariable getVariable(final Term term) {

        final Operator operator = term.op();

        /*
         * Process an instance of ProgramVariable (most often, this will be a
         * LocationVariable). Such an object will represent a non-static field
         * of some class, and its parent is as such simply an instance of that
         * class.
         */
        if (operator instanceof ProgramVariable) {

            /*
             * KeY represents the heap as a LocationVariable as well. We
             * cannot(?) do anything useful with it, so we ignore it. However,
             * if the LocationVariable correspons to "self" (i.e. the root
             * variable), we return the default root, although we first properly
             * set the type (which is not needed, but nice to have).
             */
            final String operatorName = operator.toString();
            if (!operatorName.equalsIgnoreCase("heap")) {

                if (operator.toString().equalsIgnoreCase("self")) {

                    return default_self;
                } else {
                    return (ProgramVariable) operator;
                }
            }
        }

        /*
         * Process a normal Function. This step is necessary since the root
         * instance of the class holding the method under test (i.e. "self")
         * will be of this type. If self is encountered, insert a placebo
         * variable for it (since KeY does not always create a native variable
         * for it).
         */
        if (operator.getClass() == Function.class) {

            if (operator.toString().equalsIgnoreCase("self")) {

                return default_self;
            }
        }

        /*
         * Process a SortDependingFunction. A Term of this sort represents a
         * recursively defined variable (i.e. a variable at the end of a nested
         * hiearchy, such as self.nestedObject.anotherNestedObject.variable).
         */
        if (operator.getClass() == SortDependingFunction.class) {

            return getProgramVariableForField(term.sub(2));
        }

        return null;
    }

    /**
     * Parse a {@link Term} representing a program variable. Such a Term can be
     * either a plain local declaration (i.e. a {@link LocationVariable} ), or
     * it can be part of a nested hierarchy (i.e. a
     * {@link SortDependingFunction}). We treat both cases here.
     * 
     * @param term
     *            the term to parse
     */
    private void parseVariableTerm(final Term term) {

        /*
         * If the program variable instance resolves to null, it does not
         * correspond to a variable type recognized by KeYTestGen (this is
         * likely to change in the future).
         * 
         * Also, if the variable corresponds to the root type, we do not process
         * it (since it is already part of the model by default.
         * 
         * FIXME: There must be a cleaner way of checking if the root variable
         * has been found - this is a terribly ugly hack. Check if sort is null
         * instead? What other variables (if any) may have nulled sorts?
         */
        final ProgramVariable programVariable = getVariable(term);

        if ((programVariable == null)
                || programVariable.toString().equals("self")) {
            return;
        }

        /*
         * Create the variable itself, together with its corresponding instance.
         * If the variable is a primitive type, a corresponding wrapper class
         * has to be generated in order to represent its value. If it is not
         * primitive, we simply create a new ModelInstance to hold any reference
         * object.
         */
        final String identifier = TermParserTools.resolveIdentifierString(term,
                TermToModelVisitor.SEPARATOR);

        /*
         * Check that the variable we found is not already present in the model.
         */
        final ModelVariable currentVariable = model.getVariable(identifier);
        if ((currentVariable != null) && currentVariable.isParameter()) {
            return;
        }

        final ModelVariable variable = ModelVariable.constructModelVariable(
                programVariable, identifier);

        Object instance = null;
        if (TermParserTools.isPrimitiveType(term)) {

            /*
             * The term is a static variable. Identify and connect it with
             */

            instance = TermToModelVisitor.resolvePrimitiveType(programVariable);

        } else {

            instance = ModelInstance.constructModelInstance(programVariable.getKeYJavaType());
        }

        /*
         * Add the variable and its instance to the Model. This might seem
         * premature, but must be done to preserve referential integrity and
         * avoiding extra work.
         */
        model.add(variable, instance);

        /*
         * If the term is a SortDependingFunction, we are faced with two
         * possibilities:
         * 
         * 1. the variable in question may be a field of some instance. In this
         * case, we attempt to resolve the variable pointing to this instance,
         * in order to add the our newly created variable as a field of that
         * instance.
         * 
         * 2. the variable is null, in which case this variable must be a static
         * field of its declaring class. In this case, it is not part of any
         * instance, and we let the parent remain null.
         */
        if (TermParserTools.isSortDependingFunction(term)) {

            final ProgramVariable parentVariable = getVariable(term.sub(1));

            /*
             * The parent is not null, and this variable is hence an instance
             * variable of some class. Connect it to the parent.
             */
            if (parentVariable != null) {

                final String parentIdentifier = TermParserTools.resolveIdentifierString(
                        term.sub(1), TermToModelVisitor.SEPARATOR);

                final ModelVariable parentModelVariable = ModelVariable.constructModelVariable(
                        parentVariable, parentIdentifier);

                model.assignField(variable, parentModelVariable);

            } else if (!programVariable.isStatic()) {

                final ModelVariable self = ModelVariable.constructModelVariable(
                        default_self, "self");
                model.assignField(variable, self);
            }
        }

        /*
         * Finally, if the variable was not a SortDependentFunction (i.e. did
         * not have an explicitly declared parent), we check if its name
         * corresponds to the names of any of the parameters for the method we
         * are currently dealing with. If that is not the case, we deduce that
         * it is a locally declared variable, and hence set its parent to be the
         * root class.
         * 
         * If the variable indeed is a parameter, we create a separate variable
         * and instance for it.
         */
        else {

            final ModelVariable self = ModelVariable.constructModelVariable(
                    default_self, "self");
            model.assignField(variable, self);

        }
    }

    /**
     * Visit a {@link Term} node, extracting any data related to
     * {@link ProgramVariable} instances in this node, if any. If such data is
     * found, it will be encoded in a {@link ModelVariable} format.
     * <p>
     * <strong>IMPORTANT:</strong> Due to how {@link Term} ASTs are implemented,
     * this method will only have the desired effect if the visitation is
     * carried out in postorder. Preorder will cause the Model to be constructed
     * with wrong parent-child relationships.
     * <p>
     * To achieve correct results, thus, please only pass this visitor as a
     * parameter to {@link Term#execPostOrder(de.uka.ilkd.key.logic.Visitor)}
     * <p>
     */
    @Override
    public void visit(final Term visited) {

        if (TermParserTools.isVariable(visited)) {
            parseVariableTerm(visited);
        }
    }
}