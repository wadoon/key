package de.uka.ilkd.key.testgeneration.util.parsers.transformers;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.testgeneration.util.parsers.TermParserTools;

public class RemoveSDPsTransformer extends AbstractTermTransformer {

    private final String SEPARATOR;

    public RemoveSDPsTransformer(final String separator) {

        this.SEPARATOR = separator;
    }

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
    public Term transform(final Term term) throws TermTransformerException {

        return this.transformTerm(term);
    }

    @Override
    protected Term transformSortDependentFunction(final Term term) {

        final ProgramElementName resolvedVariableName = new ProgramElementName(
                TermParserTools.resolveIdentifierString(term, this.SEPARATOR));

        final LocationVariable resolvedVariable = new LocationVariable(
                resolvedVariableName, term.sort());

        return this.termFactory.createTerm(resolvedVariable);
    }
}