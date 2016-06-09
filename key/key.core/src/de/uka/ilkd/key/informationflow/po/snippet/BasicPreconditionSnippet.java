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
class BasicPreconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.PRECONDITION) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "precondition for a contract without precondition.");
        }
        assert JavaDLTerm.class.equals(BasicSnippetData.Key.PRECONDITION.getType());
        JavaDLTerm origPre = (JavaDLTerm) d.get(
                BasicSnippetData.Key.PRECONDITION);
        return replace(origPre, d.origVars, poVars.pre, d.tb);
    }
}