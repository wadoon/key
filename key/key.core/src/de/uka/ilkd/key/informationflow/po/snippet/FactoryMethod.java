package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 *
 * @author christoph
 */
interface FactoryMethod {

    JavaDLTerm produce(BasicSnippetData d,
                 ProofObligationVars poVars)
            throws UnsupportedOperationException;
}
