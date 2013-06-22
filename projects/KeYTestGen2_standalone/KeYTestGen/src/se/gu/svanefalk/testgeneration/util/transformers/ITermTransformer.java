package se.gu.svanefalk.testgeneration.util.transformers;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.TermTransformer;

/**
 * Implementors of this interface represent objects which are capable of
 * transforming the structure of {@link Term}s.
 * <p>
 * Not to be confused with {@link TermTransformer}.
 * 
 * @author christopher
 * 
 */
public interface ITermTransformer {

    public Term transform(Term term) throws TermTransformerException;

}
