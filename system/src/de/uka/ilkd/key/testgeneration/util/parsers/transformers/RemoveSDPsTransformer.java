package de.uka.ilkd.key.testgeneration.util.parsers.transformers;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

public class RemoveSDPsTransformer extends AbstractTermTransformer {

    private final String SEPARATOR;

    /**
     * Removes all instances of {@link SortDependingFunction} nodes in a given
     * term, replacing them with {@link LocationVariable} instances whose names
     * will correspond to the nesting hiearchy expressed in the
     * SortDependingFunction they correspond to.
     * 
     * @param term
     *            the term
     * @return the term with all SortDependingFunctions removed
     */
    @Override
    public Term transform(Term term) throws TermTransformerException {

        return transformTerm(term);
    }

    public RemoveSDPsTransformer(String separator) {

        this.SEPARATOR = separator;
    }

    @Override
    protected Term transformSortDependentFunction(final Term term) {

        ProgramElementName resolvedVariableName = new ProgramElementName(
                resolveIdentifierString(term, SEPARATOR));

        LocationVariable resolvedVariable = new LocationVariable(
                resolvedVariableName, term.sort());

        return termFactory.createTerm(resolvedVariable);
    }
}