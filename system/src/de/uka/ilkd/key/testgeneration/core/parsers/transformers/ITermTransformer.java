package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import de.uka.ilkd.key.logic.Term;

/**
 * Implementors of this interface represent objects which are capable of
 * transforming the structure of {@link Term}s.
 * 
 * @author christopher
 * 
 */
public interface ITermTransformer {

    public Term transform(Term term) throws TermTransformerException;

}
