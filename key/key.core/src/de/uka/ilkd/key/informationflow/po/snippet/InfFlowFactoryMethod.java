package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 *
 * @author christoph
 */
interface InfFlowFactoryMethod {

    JavaDLTerm produce(BasicSnippetData d,
                 ProofObligationVars poVars1,
                 ProofObligationVars poVars2)
            throws UnsupportedOperationException;
}
