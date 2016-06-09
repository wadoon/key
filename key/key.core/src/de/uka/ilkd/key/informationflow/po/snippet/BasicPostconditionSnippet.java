/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicPostconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.POSTCONDITION) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "postcondition for a contract without postcondition.");
        }
        assert JavaDLTerm.class.equals(BasicSnippetData.Key.POSTCONDITION.getType());
        JavaDLTerm origPost = (JavaDLTerm) d.get(
                BasicSnippetData.Key.POSTCONDITION);
        return replace(origPost, d.origVars, poVars.post, d.tb);
    }
}
