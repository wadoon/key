package de.uka.ilkd.key.testgeneration.core.parsers.transformers;

import de.uka.ilkd.key.logic.Term;

/**
 * This transformer brings a Term into Negation Normal Form.
 * <p>
 * A Term is in NNF iff. the only negations it contains are negations of logical
 * atoms.
 * 
 * The algorithm used in this particular implementation was taken from:
 * <p>
 * (Huth and Ryan, <i>Logic in Computer Science</i>, 2nd Ed. Cambridge
 * University press, 2008)
 * 
 * @author christopher
 */
public class NNFTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(Term term) throws TermTransformerException {
        // TODO Auto-generated method stub
        return null;
    }
    
    @Override
    protected Term transformNot(Term term) throws TermTransformerException {
        // TODO Auto-generated method stub
        return super.transformNot(term);
    }
}
