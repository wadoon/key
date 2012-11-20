package de.uka.ilkd.key.testgeneration.visitors;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.testgeneration.model.implementation.Model;
import de.uka.ilkd.key.testgeneration.model.implementation.ModelVariable;
import de.uka.ilkd.key.testgeneration.parsers.PathconditionParser;

/**
 * This Visitor walks a {@link Term} and extracts information related to the program variables
 * represented in the term. The goal of this procedure is to provide sufficient information for
 * later constructing a {@link Model} including the extracted variables.
 * 
 * @author christopher
 */
public class TermModelVisitor
        extends KeYTestGenTermVisitor {

    public List<ModelVariable> getModelSkeleton() {

        return modelVariables;
    }

    /**
     * Stores Java specific information related to the {@link Term} we are working with.
     */
    private final JavaInfo javaInfo;

    /**
     * The extracted variables, encoded as {@link ModelVariable} instances.
     */
    List<ModelVariable> modelVariables = new LinkedList<ModelVariable>();

    public TermModelVisitor(Services services) {

        javaInfo = services.getJavaInfo();
    }

    /**
     * Visit a {@link Term} node, extracting any data related to {@link ProgramVariable} instances
     * in this node, if any. If such data is found, it will be encoded in a {@link ModelVariable}
     * format.
     * <p>
     * <strong>IMPORTANT:</strong> Due to how {@link Term} ASTs are implemented, this method will
     * only have the desired effect if the visitation is carried out in postorder. Preorder will
     * cause the Model to be constructed with wrong parent-child relationships.
     * <p>
     * To achieve correct results, thus, please only pass this visitor as a parameter to
     * {@link Term#execPostOrder(de.uka.ilkd.key.logic.Visitor)}
     * <p>
     * TODO: This entire class should be re-implemented as a one-way parser. See
     * {@link PathconditionParser}.
     */
    @Override
    public void visit(Term visited) {

        if (isVariable(visited)) {

            ProgramVariable programVariable = getVariable(visited);
            if (programVariable == null) {
                return;
            }

            String identifier = resolveIdentifierString(visited);

            /*
             * If the term is a SortDependingFunction, then it can potentially have an encapsulating
             * instance class (i.e. its parent) (if this instance is null, then the term corresponds
             * to a static variable). In this case we need to resolve the parent as well.
             */
            if (visited.op().getClass() == SortDependingFunction.class) {

                ProgramVariable parentVariable = getVariable(visited.sub(1));

                ModelVariable parentModelVariable = null;
                if (parentVariable != null) {
                    String parentIdentifier = resolveIdentifierString(visited.sub(1));
                    parentModelVariable =
                            new ModelVariable(parentVariable, null, parentIdentifier);
                }

                addToList(new ModelVariable(programVariable,
                        parentModelVariable,
                        identifier));
            }

            /*
             * Otherwise, the term represents a locally declared variable.
             */
            else {
                addToList(new ModelVariable(programVariable, null, identifier));
            }
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
        Sort sort = term.sort();

        /*
         * Process an instance of ProgramVariable (most often, this will be a LocationVariable).
         * Such an object will represent a non-static field of some class, and its parent is as such
         * simply an instance of that class.
         */
        if (operator instanceof ProgramVariable) {

            /*
             * Key represents the heap as a LocationVariable as well. We cannot(?) do anything
             * useful with it, so we ignore it.
             */
            if (!operator.toString().equalsIgnoreCase("heap")
                    && !operator.toString().equalsIgnoreCase("self")) {
                return (ProgramVariable) operator;
            }
        }

        /*
         * Process a normal Function. This step is necessary since the root instance of the class
         * holding the method under test (i.e. "self") will be of this type. If self is encountered,
         * insert a placebo variable for it (since KeY does not always create a native variable for
         * it).
         * 
         * FIXME: not needed, but perhaps keep if Model needs refactoring?
         */
        if (operator.getClass() == Function.class) {
            if (operator.toString().equalsIgnoreCase("self")) {}
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
     * Works around the fact that KeY inserts the "$" sign into {@link Term}s, which messes with the
     * variable lookup of the {@link JavaInfo} instance.
     * 
     * @param term
     *            a {@link Term} with a sort of type Field
     * @return the {@link ProgramVariable} instance corresponding to the field represented by the
     *         Term
     */
    private ProgramVariable getProgramVariableForField(Term term) {

        if (!term.sort().name().toString().equalsIgnoreCase("Field")) {
            return null;
        }

        String[] split = term.op().toString().split("::\\$");
        return javaInfo.getAttribute(split[1], split[0]);
    }

    /**
     * Add a {@link ModelVariable} to {@link #modelVariables}, allowing no duplicates.
     * 
     * @param modelVariable
     *            the {@link ModelVariable} to insert
     */
    private void addToList(ModelVariable modelVariable) {

        if (!modelVariables.contains(modelVariable)) {
            modelVariables.add(modelVariable);
        }
    }
}