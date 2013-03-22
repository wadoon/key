package se.gu.svanefalk.testgeneration.util.parsers.transformers;

import se.gu.svanefalk.testgeneration.StringConstants;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

public class RemoveSDPsTransformer extends AbstractTermTransformer {

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
                TermParserTools.resolveIdentifierString(term, StringConstants.FIELD_SEPARATOR));

        final LocationVariable resolvedVariable = new LocationVariable(
                resolvedVariableName, term.sort());

        return this.termFactory.createTerm(resolvedVariable);
    }
}