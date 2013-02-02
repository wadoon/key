package de.uka.ilkd.key.testgeneration.parsers;

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
    public Term removeSortDependingFunctions(Term term)
            throws TermTransformerException {

        return transformTerm(term);
    }
    
    @Override
    protected Term transformSortDependentFunction(Term term) {
       
            ProgramElementName resolvedVariableName = new ProgramElementName(
                    resolveIdentifierString(term));

            LocationVariable resolvedVariable = new LocationVariable(
                    resolvedVariableName, term.sort());

            System.out.println(resolvedVariable);
            return termFactory.createTerm(resolvedVariable);
        
    }
}