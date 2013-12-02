package com.csvanefalk.keytestgen.util.transformers;

import com.csvanefalk.keytestgen.StringConstants;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

public class RemoveSDPsTransformer extends AbstractTermTransformer {

    private static RemoveSDPsTransformer instance = null;

    public static RemoveSDPsTransformer getInstance() {
        if (RemoveSDPsTransformer.instance == null) {
            RemoveSDPsTransformer.instance = new RemoveSDPsTransformer();
        }
        return RemoveSDPsTransformer.instance;
    }

    private RemoveSDPsTransformer() {
    }

    /**
     * Removes all instances of {@link SortDependingFunction} nodes in a given
     * term, replacing them with {@link LocationVariable} instances whose names
     * will correspond to the nesting hiearchy expressed in the
     * SortDependingFunction they correspond to.
     *
     * @param term the term
     * @return the term with all SortDependingFunctions removed
     */
    @Override
    public Term transform(final Term term) throws TermTransformerException {

        if (term == null) {
            return term;
        }

        return transformTerm(term);
    }

    @Override
    protected Term transformProgramMethod(final Term term) {

        /*
         * Transform the object instance which this method is being invoked
         * from.
         */
        final Term parentObject = term.sub(1);

        final ProgramElementName parentObjectIdentifier = new ProgramElementName(
                TermParserTools.resolveIdentifierString(parentObject,
                        StringConstants.FIELD_SEPARATOR));

        final LocationVariable transformedParentObjectVariable = new LocationVariable(
                parentObjectIdentifier, parentObject.sort());

        final Term transformedParentObject = termFactory.createTerm(transformedParentObjectVariable);

        /*
         * Construct a new list of children for the new method term
         */
        final Term[] childBuffer = new Term[term.subs().size()];
        for (int i = 0; i < term.subs().size(); i++) {

            /*
             * Skip the second child, as this corresponds to the old parent
             * object.
             */
            if (i != 1) {
                childBuffer[i] = term.sub(i);
            }

            /*
             * If the second child is encountered, replace it with the new
             * parent object.
             */
            else {
                childBuffer[i] = transformedParentObject;
            }
        }
        final ImmutableArray<Term> newChildren = new ImmutableArray<Term>(
                childBuffer);

        return termFactory.createTerm(term.op(), newChildren, term.boundVars(),
                term.javaBlock());
    }

    @Override
    protected Term transformSortDependentFunction(final Term term) {

        final ProgramElementName resolvedVariableName = new ProgramElementName(
                TermParserTools.resolveIdentifierString(term,
                        StringConstants.FIELD_SEPARATOR));

        final LocationVariable resolvedVariable = new LocationVariable(
                resolvedVariableName, term.sort());

        return termFactory.createTerm(resolvedVariable);
    }
}