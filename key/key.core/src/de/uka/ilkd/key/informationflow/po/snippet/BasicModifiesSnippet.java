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
class BasicModifiesSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.MODIFIES) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "modifies-term for a contract without modifies.");
        }
        assert JavaDLTerm.class.equals(BasicSnippetData.Key.MODIFIES.getType());
        JavaDLTerm origMod = (JavaDLTerm) d.get(BasicSnippetData.Key.MODIFIES);
        return replace(origMod, d.origVars, poVars.pre, d.tb);
    }
}
