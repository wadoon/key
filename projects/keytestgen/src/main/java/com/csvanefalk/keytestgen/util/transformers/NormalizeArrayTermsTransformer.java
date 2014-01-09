package com.csvanefalk.keytestgen.util.transformers;

import de.uka.ilkd.key.logic.Term;

/**
 * Created by christopher on 08/01/14.
 * <p/>
 * Normalizes Array accessors by turning them into more "natural" representations
 * such as "arr[0]" instead of, for example, int::select(heap,array,arr(Z(0(#)).
 */
public class NormalizeArrayTermsTransformer extends AbstractTermTransformer {

    @Override
    public Term transform(final Term term) throws TermTransformerException {
        return null;
    }
}
