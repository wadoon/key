package de.uka.ilkd.key.testgeneration.core.model.implementation;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.testgeneration.StringConstants;
import de.uka.ilkd.key.testgeneration.core.model.IModel;
import de.uka.ilkd.key.testgeneration.core.model.IModelGenerator;
import de.uka.ilkd.key.testgeneration.core.model.ModelGeneratorException;
import de.uka.ilkd.key.testgeneration.core.model.tools.EliminateConjunctionsTransformer;
import de.uka.ilkd.key.testgeneration.core.model.tools.ModelGenerationTools;
import de.uka.ilkd.key.testgeneration.util.parsers.TermParserException;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.NegationNormalFormTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.RemoveIfThenElseTransformer;
import de.uka.ilkd.key.testgeneration.util.parsers.transformers.TermTransformerException;
import de.uka.ilkd.key.testgeneration.util.parsers.visitors.KeYTestGenTermVisitor;

/**
 * Given that a client does not specify anything else, KeYTestGen2 will default
 * to this implementation of {@link IModelGenerator} for the purpose of
 * instantiating path conditions.
 * <p>
 * This particular implementation makes use of SMT solvers in order to
 * facilitate model generation. The pathcondition to be instantiated is
 * translated into the SMT-LIB2 language, and the KeY SMT interface is
 * subsequently invoked in order to find an assignment of variables that satisfy
 * the pathcondition (if such an assignment exits).
 * <p>
 * The set of assignments found are further processed into an instance of
 * {@link IModel}, which constitutes the final representaiton of the model.
 */
public class ModelGenerator implements IModelGenerator {

    /**
     * The solvers assigned to the ModelGenerator.
     */
    private final SolverType[] solvers;

    /**
     * The settings for the SMT solvers. These follow a default implementation,
     * although it is possible for the user to use custom settings.
     */
    private final SMTSettings settings;

    /**
     * Backend constructo, used by the factory methods.
     * 
     * @param solvers
     *            the solvers to use
     * @param settings
     *            the settings for the used solvers
     */
    private ModelGenerator(final SMTSettings settings,
            final SolverType... solvers) {

        this.solvers = solvers;
        this.settings = settings;
    }

    /**
     * Creates a default implementation of the ModelGenerator, which uses the Z3
     * solvers with default settings.
     * 
     * @return a default instance of ModelGenerator
     * @throws ModelGeneratorException
     */
    public static ModelGenerator getDefaultModelGenerator() {

        return new ModelGenerator(ModelSettings.getDEFAULT_SMT_SETTINGS(),
                SolverType.Z3_SOLVER);
    }

    /**
     * Creates a custom implementation of the ModelGenerator. The user specifies
     * which SMT solvers(s) and what settings should be used
     * <p>
     * TODO: Currently only the Z3 solver will return a model, implement this
     * for the other supported solvers as well.
     * 
     * @param settings
     *            The settings for the SMT solvers used
     * @return a custom instance of the ModelGenerator
     * @throws ModelGeneratorException
     */
    public ModelGenerator getCustomModelGenerator(final SMTSettings settings,
            final SolverType... solvers) throws ModelGeneratorException {

        verifySolverAvailability(solvers);

        return new ModelGenerator(settings, solvers);
    }

    /**
     * This method takes a {@link Model} instance, and <i>instantiates</i> this
     * Model using the output of an SMT solver, here represented by
     * {@link SMTSolverResult}.
     * <p>
     * Instantiation means that any concrete values of <i>primitive</i> values
     * represented in the Model will be extracted from the SMT solver result and
     * inserted into their respective locations in the Model. The precise
     * location of a given value instantiation is determined by the
     * <i>identifier</i> String associated with the value. A concrete value
     * belonging to a specific {@link ModelVariable} instance will have the same
     * identifier as that variable.
     * 
     * @param model
     *            the Model to instantiate
     * @param smtResult
     *            the output of an SMT solver
     * @return the instantiated Model
     * @throws ModelGeneratorException
     *             in the event that the instantiation went wrong
     */
    private Model instantiateModel(final Model model,
            final SMTSolverResult smtResult) {

        String modelOutput = consolidateModelOutput(smtResult.getOutput());
        model.consumeSMTOutput(modelOutput);
        return model;
    }

    /**
     * Creates an {@link SMTProblem} from a {@link Term} representing a path
     * condition for an {@link IExecutionNode}.
     * 
     * @param targetNode
     *            the node for which to generate an SMT problem.
     * @return an SMTProblem corresponding to the path condition of the node
     * @throws ModelGeneratorException
     *             in the event that the SMT problem cannot be generated
     */
    private synchronized SMTProblem createSMTProblem(Term pathCondition)
            throws ModelGeneratorException {

        /*
         * The path condition has to be negated, in order to undo the negations
         * that will be carried out by the SMT interface.
         */
        pathCondition = TermFactory.DEFAULT.createTerm(Junctor.NOT,
                pathCondition);

        return new SMTProblem(pathCondition);

    }

    private synchronized SMTSolverResult solveSMTProblem(
            final SMTProblem problem, final Services services)
            throws ModelGeneratorException {

        SMTSolverResult result = null;

        /*
         * Used for keeping track of the number of attempts at model generation
         * so far.
         */
        int attempts = 1;

        /*
         * Assert that we could actually find a satisfiable assignment for the
         * SMT problem. If not, keep trying until we do
         */
        do {

            /*
             * Start the constraint solving procedure, the solution will be
             * encapsulated in the existing SMTProblem.
             */
            try {

                /*
                 * Set up a SolverLauncher for the purpose of interfacing with
                 * the associated SMT solvers.
                 */
                SolverLauncher launcher = new SolverLauncher(settings);

                launcher.launch(problem, services, SolverType.Z3_SOLVER);

                result = problem.getFinalResult();

            } catch (RuntimeException re) {

                /*
                 * In the event that the system fails due launchers being
                 * reused, dispose of them and create new ones.
                 */
                System.err.println(re.getMessage());
                re.printStackTrace();
                continue;
            }

            if (!result.isValid().equals(ThreeValuedTruth.FALSIFIABLE)) {
                System.err.println("Failed to retrieve adequate SMT solution");
            }

            if (attempts > 1) {
                System.err.println("New attempt: " + attempts);
            }
            attempts++;

        } while (result.isValid().equals(ThreeValuedTruth.UNKNOWN)
                && attempts < ModelSettings.getNUMBER_OF_TRIES());

        /*
         * If the path condition is not satisfiable (should never happen), then
         * signal this with an exception. Mostly for debug and reliability
         * reasons.
         */
        if (result.isValid().equals(ThreeValuedTruth.UNKNOWN)
                || result.isValid().equals(ThreeValuedTruth.VALID)) {

            throw new ModelGeneratorException(
                    "Could not generate model for this path condition: "
                            + problem.getTerm());
        }

        return result;
    }

    /**
     * Assert that the solvers associated with the ModelGenerator are
     * accessible.
     * 
     * @param solvers
     * @throws ModelGeneratorException
     */
    private static void verifySolverAvailability(final SolverType... solvers)
            throws ModelGeneratorException {

        for (SolverType solver : solvers) {
            if (!solver.isInstalled(false)) {
                throw new ModelGeneratorException(
                        "Solver "
                                + solver.getName()
                                + " is not installed or could not be accessed. Check paths?");
            }
        }
    }

    /**
     * Returns an {@link SMTSolverResult} for the pathcondition of a given
     * {@link IExecutionNode}. This result will represent a concrete assignment
     * of primitive values in the pathcondition, such that the constraint
     * represented by the pathcondition becomes satisifed.
     * <p>
     * We are not interested in the shape of the solved contraint per se, rather
     * we will use these concrete values to instantiate our {@link Model}.
     * 
     * @param node
     *            the node whose pathpathcondition to instantiate
     * @return the SMT solver result
     * @throws ModelGeneratorException
     */
    private SMTSolverResult instantiatePathCondition(final Term pathCondition,
            final Services services) throws ModelGeneratorException {

        try {

            /*
             * Simplify the path condition. If the simplified path condition is
             * null, this means that it does not contain any primitive values.
             * There is hence nothing useful we can do with it, and we just
             * return it as null.
             */
            Term simplifiedPathCondition = ModelGenerationTools
                    .simplifyTerm(pathCondition);

            if (simplifiedPathCondition == null) {

                return null;

            } else {

                /*
                 * Turn the path condition of the node into a constraint problem
                 */
                SMTProblem problem = createSMTProblem(simplifiedPathCondition);

                /*
                 * Solve the constraint and return the result
                 */
                return solveSMTProblem(problem, services);
            }

        } catch (TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * generates a {@link Model} for the pathcondition of a single
     * {@link IExecutionNode}, i.e. a single program statement.
     * 
     * @param node
     *            the node for which to generate a Model
     * @param mediator
     *            session mediator
     * @return the Model instance for the node
     * @throws ModelGeneratorException
     *             in the event that there was a failure to generate the Model
     */
    @Override
    public Model generateModel(final IExecutionNode node)
            throws ModelGeneratorException {

        try {

            Term pathCondition = node.getPathCondition();
            Services services = node.getServices();

            /*
             * Create the initial Model, without any concrete values assigned to
             * primitive integer values in it.
             */
            Model model = new TermToModelConverter().createModel(node);

            /*
             * Get concrete values for any primitive types represented in the
             * Model, extracting them from an SMT solution for the pathcondition
             * for this node.
             */
            SMTSolverResult solverResult = instantiatePathCondition(
                    pathCondition, services);

            /*
             * If any such primitive values were found, merge their concrete
             * values into the Model
             */
            if (solverResult != null) {
                return instantiateModel(model, solverResult);
            } else {
                return model;
            }
        } catch (ProofInputException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        }
    }

    /**
     * Concatenates the output of the SMT solver into a single String.
     * 
     * @param output
     *            the ouput of the solver
     * @return the consolidated String
     */
    private String consolidateModelOutput(final List<String> output) {

        StringBuilder stringBuilder = new StringBuilder();
        for (String substring : output) {
            stringBuilder.append(substring);
        }
        return stringBuilder.toString();
    }

    private static class TermToModelConverter {

        /**
         * Creates a skeletal {@link Model} instance from a {@link Term}. The
         * Term will be parsed, and all representations of program variables
         * (along with their relationships to one another) will be used to
         * construct a "skeletal" Model instance (i.e. no concrete primitive
         * values).
         * 
         * @param term
         *            the Term to process
         * @param services
         *            {@link Services} associated with the Term
         * @param mediator
         *            session mediator
         * @return the Model instance built from the Term
         * @throws TermTransformerException
         * @throws ProofInputException
         */
        public static Model createModel(IExecutionNode node)
                throws TermTransformerException, ProofInputException {

            Term pathCondition = node.getPathCondition();

            Model model = new Model();

            /*
             * Remove if-then-else statements from the pathcondition
             */
            pathCondition = new RemoveIfThenElseTransformer()
                    .transform(pathCondition);

            /*
             * Construct the initial Model, containing representation of all the
             * variables and values found in the Term. Done postorder to
             * eliminate buffering penalties in the Model.
             */
            TermToModelVisitor modelVisitor = new TermToModelVisitor(model,
                    node);
            pathCondition.execPostOrder(modelVisitor);

            /*
             * Distribute negations and remove conjunctions
             */
            pathCondition = new NegationNormalFormTransformer()
                    .transform(pathCondition);
            pathCondition = new EliminateConjunctionsTransformer()
                    .transform(pathCondition);

            /*
             * Setup all reference relationships expressed in the Term. Done
             * preorder to correctly handle non-assigning operations, such as
             * not-equals.
             */
            ResolveVariableAssignmentVisitor referenceVisitor = new ResolveVariableAssignmentVisitor(
                    model);
            pathCondition.execPreOrder(referenceVisitor);

            return modelVisitor.getModel();
        }

        // *******VISITORS*******

        /**
         * This Visitor walks a {@link Term} and extracts information related to
         * the program variables represented in the term. The goal of this
         * procedure is to provide sufficient information for later constructing
         * a {@link Model} including the extracted variables.
         * 
         * @author christopher
         */
        private static class TermToModelVisitor extends KeYTestGenTermVisitor {

            /**
             * Constant for separating fields in {@link SortDependingFunction}
             * instances.
             */
            private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR
                    .toString();

            /**
             * Stores Java specific information related to the {@link Term} we
             * are working with.
             */
            private final JavaInfo javaInfo;

            /**
             * The default root variable, representing a reference to the class
             * instance of which the tested method is part.
             */
            private final LocationVariable default_self;

            /**
             * The {@link Model} to be populated by visiting the associated
             * Term.
             */
            Model model;

            public TermToModelVisitor(Model model, IExecutionNode node) {

                IExecutionMethodCall methodCall = getMethodCallNode(node);

                this.model = model;

                this.javaInfo = methodCall.getServices().getJavaInfo();

                /*
                 * Construct the default base class.
                 */
                KeYJavaType container = methodCall.getProgramMethod()
                        .getContainerType();

                default_self = new LocationVariable(new ProgramElementName(
                        "$SELF$"), new KeYJavaType(container));

                /*
                 * Add the root variable and instance to the Model
                 */
                ModelInstance selfInstance = new ModelInstance(container);

                ModelVariable self = new ModelVariable(default_self, "self",
                        selfInstance);

                model.add(self, selfInstance);

                /*
                 * Insert the method parameters by default. Their value do not
                 * matter at this stage, as they will be instantiated later as
                 * needed.
                 */
                ImmutableArray<ParameterDeclaration> parameterDeclarations = methodCall
                        .getProgramMethod().getParameters();

                for (ParameterDeclaration parameterDeclaration : parameterDeclarations) {

                    for (VariableSpecification variableSpecification : parameterDeclaration
                            .getVariables()) {

                        /*
                         * Convert the declaration to a program variable TODO: I
                         * DO NOT WANT TO HAVE TO FLIPFLOP BETWEEN DIFFERENT
                         * ABSTRACTIONS!
                         */
                        KeYJavaType type = new KeYJavaType(
                                variableSpecification.getType());

                        ProgramElementName name = new ProgramElementName(
                                variableSpecification.getName());

                        IProgramVariable programVariable = new LocationVariable(
                                name, type);

                        ModelVariable modelParameter = new ModelVariable(
                                programVariable, name.toString());

                        modelParameter.setParameter(true);

                        /*
                         * The parameter is primitive.
                         */

                        Object value = null;
                        if (primitiveTypes.contains(modelParameter.getType())) {
                            value = resolvePrimitiveType(programVariable);
                        }
                        model.add(modelParameter, value);
                    }
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
             * Visit a {@link Term} node, extracting any data related to
             * {@link ProgramVariable} instances in this node, if any. If such
             * data is found, it will be encoded in a {@link ModelVariable}
             * format.
             * <p>
             * <strong>IMPORTANT:</strong> Due to how {@link Term} ASTs are
             * implemented, this method will only have the desired effect if the
             * visitation is carried out in postorder. Preorder will cause the
             * Model to be constructed with wrong parent-child relationships.
             * <p>
             * To achieve correct results, thus, please only pass this visitor
             * as a parameter to
             * {@link Term#execPostOrder(de.uka.ilkd.key.logic.Visitor)}
             * <p>
             */
            @Override
            public void visit(Term visited) {

                if (isVariable(visited)) {
                    parseVariableTerm(visited);
                }
            }

            /**
             * Parse a {@link Term} representing a program variable. Such a Term
             * can be either a plain local declaration (i.e. a
             * {@link LocationVariable} ), or it can be part of a nested
             * hierarchy (i.e. a {@link SortDependingFunction}). We treat both
             * cases here.
             * 
             * @param term
             *            the term to parse
             */
            private void parseVariableTerm(Term term) {

                /*
                 * If the program variable instance resolves to null, it does
                 * not correspond to a variable type recognized by KeYTestGen
                 * (this is likely to change in the future).
                 * 
                 * Also, if the variable corresponds to the root type, we do not
                 * process it (since it is already part of the model by default.
                 * 
                 * FIXME: There must be a cleaner way of checking if the root
                 * variable has been found - this is a terribly ugly hack. Check
                 * if sort is null instead? What other variables (if any) may
                 * have nulled sorts?
                 */
                ProgramVariable programVariable = getVariable(term);

                if (programVariable == null
                        || programVariable.toString().equals("$SELF$")) {
                    return;
                }

                /*
                 * Create the variable itself, together with its corresponding
                 * instance. If the variable is a primitive type, a
                 * corresponding wrapper class has to be generated in order to
                 * represent its value. If it is not primitive, we simply create
                 * a new ModelInstance to hold any reference object.
                 */
                String identifier = resolveIdentifierString(term, SEPARATOR);

                ModelVariable variable = new ModelVariable(programVariable,
                        identifier);

                Object instance = null;
                if (isPrimitiveType(term)) {

                    instance = resolvePrimitiveType(programVariable);
                } else {
                    instance = new ModelInstance(
                            programVariable.getKeYJavaType());
                }

                /*
                 * Add the variable and its instance to the Model. This might
                 * seem premature, but must be done to preserve referential
                 * integrity and avoiding extra work.
                 */
                model.add(variable, instance);

                /*
                 * If the term is a SortDependingFunction, we are faced with two
                 * possibilities:
                 * 
                 * 1. the variable in question may be a field of some instance.
                 * In this case, we attempt to resolve the variable pointing to
                 * this instance, in order to add the our newly created variable
                 * as a field of that instance.
                 * 
                 * 2. the variable is null, in which case this variable must be
                 * a static field of its declaring class. In this case, it is
                 * not part of any instance, and we let the parent remain null.
                 */
                if (isSortDependingFunction(term)) {

                    ProgramVariable parentVariable = getVariable(term.sub(1));

                    /*
                     * The parent is not null, and this variable is hence an
                     * instance variable of some class. Connect it to the
                     * parent.
                     */
                    if (parentVariable != null) {
                        String parentIdentifier = resolveIdentifierString(
                                term.sub(1), SEPARATOR);
                        ModelVariable parentModelVariable = new ModelVariable(
                                parentVariable, parentIdentifier);

                        model.assignField(variable, parentModelVariable);
                    } else if (!programVariable.isStatic()) {

                        ModelVariable self = new ModelVariable(default_self,
                                "self");
                        model.assignField(variable, self);
                    }
                }

                /*
                 * Finally, if the variable was not a SortDependentFunction
                 * (i.e. did not have an explicitly declared parent), we check
                 * if its name corresponds to the names of any of the parameters
                 * for the method we are currently dealing with. If that is not
                 * the case, we deduce that it is a locally declared variable,
                 * and hence set its parent to be the root class.
                 * 
                 * If the variable indeed is a parameter, we create a separate
                 * variable and instance for it.
                 */
                else {

                    ModelVariable self = new ModelVariable(default_self, "self");
                    model.assignField(variable, self);

                }
            }

            /**
             * Retrieve the {@link ProgramVariable} represented by a given
             * {@link Term}, if any.
             * 
             * @param term
             *            the term to process
             * @return the {@link ProgramVariable} corresponding to the Term,
             *         iff. the Term represents a variable.
             */
            private ProgramVariable getVariable(Term term) {

                Operator operator = term.op();

                /*
                 * Process an instance of ProgramVariable (most often, this will
                 * be a LocationVariable). Such an object will represent a
                 * non-static field of some class, and its parent is as such
                 * simply an instance of that class.
                 */
                if (operator instanceof ProgramVariable) {

                    /*
                     * KeY represents the heap as a LocationVariable as well. We
                     * cannot(?) do anything useful with it, so we ignore it.
                     * However, if the LocationVariable correspons to "self"
                     * (i.e. the root variable), we return the default root,
                     * although we first properly set the type (which is not
                     * needed, but nice to have).
                     */
                    if (!operator.toString().equalsIgnoreCase("heap")) {

                        if (operator.toString().equalsIgnoreCase("self")) {

                            ProgramVariable variable = (ProgramVariable) operator;
                            Type realType = variable.getKeYJavaType()
                                    .getJavaType();
                            default_self.getKeYJavaType().setJavaType(realType);

                            return default_self;
                        } else {
                            return (ProgramVariable) operator;
                        }
                    }
                }

                /*
                 * Process a normal Function. This step is necessary since the
                 * root instance of the class holding the method under test
                 * (i.e. "self") will be of this type. If self is encountered,
                 * insert a placebo variable for it (since KeY does not always
                 * create a native variable for it).
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
                 * Process a SortDependingFunction. A Term of this sort
                 * represents a recursively defined variable (i.e. a variable at
                 * the end of a nested hiearchy, such as
                 * self.nestedObject.anotherNestedObject.variable).
                 */
                if (operator.getClass() == SortDependingFunction.class) {

                    return getProgramVariableForField(term.sub(2));
                }
                return null;
            }

            /**
             * Works around the fact that KeY inserts the "$" sign into
             * {@link Term} s, which messes with the variable lookup of the
             * {@link JavaInfo} instance.
             * 
             * @param term
             *            a {@link Term} with a sort of type Field
             * @return the {@link ProgramVariable} instance corresponding to the
             *         field represented by the Term
             */
            private ProgramVariable getProgramVariableForField(Term term) {

                if (!term.sort().name().toString().equalsIgnoreCase("Field")) {
                    return null;
                }

                String[] split = term.op().toString().split("::\\$");
                return javaInfo.getAttribute(split[1], split[0]);
            }

            private ProgramVariable getProgramVariable(String name) {
                return javaInfo.getAttribute(name);
            }

            /**
             * Returns a wrapper representation of the primitive type of a
             * variable
             * 
             * @param variable
             *            the variable
             * @return the primitive type of the variable
             */
            private static Object resolvePrimitiveType(IProgramVariable variable) {

                /*
                 * FIXME: Horrible. Do not do String comparison here, find a
                 * convenient way to compare based on types.
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
                    return new Byte("0xe0");
                }
                if (typeName.equals("char")) {
                    return new Character('0');
                } else {
                    return null;
                }
            }

            /**
             * Given an {@link IExecutionNode} somewhere in a symbolic execution
             * tree and below the method call node, backtracks until the method
             * call node is found.
             * 
             * @param node
             *            the node
             * @return
             */
            private IExecutionMethodCall getMethodCallNode(IExecutionNode node) {

                if (node instanceof IExecutionMethodCall) {
                    return (IExecutionMethodCall) node;
                } else {
                    return getMethodCallNode(node.getParent());
                }
            }
        }

        /**
         * Looks for junctors in a {@link Term}, and reflects their semantic
         * meaning in the {@link Model} corresponding to the term.
         * 
         * @author christopher
         */
        private static class ResolveVariableAssignmentVisitor extends
                KeYTestGenTermVisitor {

            /**
             * Constant for separating fields in {@link SortDependingFunction}
             * instances.
             */
            private static final String SEPARATOR = StringConstants.FIELD_SEPARATOR
                    .toString();

            /**
             * Flag to indicate if we have seen a Not operator.
             */
            private boolean sawNot;

            /**
             * The {@link Model} instance associated with the Term being
             * visited. Constructed separately by an instance of
             * {@link TermToModelVisitor}.
             */
            private final Model model;

            public ResolveVariableAssignmentVisitor(Model model) {

                this.model = model;
            }

            @Override
            public void visit(Term visited) {

                if (isNot(visited)) {
                    sawNot = true;
                } else if (isEquals(visited)) {
                    parseEquals(visited);
                    sawNot = false;
                } else if (isBinaryFunction2(visited) && sawNot) {
                    sawNot = false;
                }
            }

            /**
             * Equality has to be dealt with depending on the type of the
             * <strong>left-hand</strong> variable, since this is the operand
             * which will determine the meaning of the equality.
             * <p>
             * If the variable is <strong>primitve</strong>, equality, in our
             * abstraction, implies a value assignment: equals(a,b) simply means
             * that the value of b is copied into a. For Integer types, there is
             * no need to do this explicitly, since the SMT interface will be
             * taking care of this, and we would thus only be performing the
             * same work twice. For Boolean types, however, which are not
             * resolved by the SMT interface, we do this explicitly.
             * <p>
             * If the variable is a <strong>reference</strong> type, things get
             * more interesting, since equality in this case implies that the
             * operands are pointing to a common object in memory. To represent
             * this in our abstraction, we need to cross-reference to Value
             * property of both operands, making them point to each other. We do
             * this by making sure that whatever Value is assigned to both
             * operands has the same unique identifier.
             * 
             * @param term
             *            the term to process
             */
            private void parseEquals(Term term) {

                try {

                    Term leftOperand = term.sub(0);
                    Term rightOperand = term.sub(1);

                    String leftOperandIdentifier;
                    String rightOperandIdentifier;

                    /*
                     * Process primitive variables.
                     */
                    if (isPrimitiveType(leftOperand)) {

                        /*
                         * If the left-hand hand is a boolean, configure it
                         * accordingly.
                         */
                        if (isBoolean(leftOperand)) {

                            leftOperandIdentifier = resolveIdentifierString(
                                    leftOperand, SEPARATOR);

                            /*
                             * If the right-hand operator is a boolean constant
                             * (TRUE or FALSE), we need to create a new such
                             * value and assign it to the variable.
                             */
                            if (isBooleanConstant(rightOperand)) {

                                ModelVariable modelVariable = model
                                        .getVariableByReference(leftOperandIdentifier);

                                boolean value = isBooleanTrue(rightOperand);
                                value = (sawNot) ? !value : value;
                                model.add(modelVariable, value);
                            } else {
                                // Breakpoint hook - should never happen.
                                int dummy = 1;
                                dummy++;
                            }

                            /*
                             * Process reference variables.
                             */
                        } else if (!sawNot) {

                            leftOperandIdentifier = resolveIdentifierString(
                                    leftOperand, SEPARATOR);
                            rightOperandIdentifier = resolveIdentifierString(
                                    rightOperand, SEPARATOR);

                            ModelVariable leftModelVariable = model
                                    .getVariableByReference(leftOperandIdentifier);

                            ModelVariable rightModelVariable = model
                                    .getVariableByReference(rightOperandIdentifier);

                            model.assignPointer(leftModelVariable,
                                    rightModelVariable);
                        }
                    }

                } catch (TermParserException e) {
                    // Should never happen. Caught only because
                    // AbstractTermParser requires it.
                    return;
                }
            }
        }
    }
}