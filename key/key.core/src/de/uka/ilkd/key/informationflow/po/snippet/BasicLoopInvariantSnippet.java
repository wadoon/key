package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicLoopInvariantSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.LOOP_INVARIANT) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "loop invariant for a loop without invariant.");
        }
        assert JavaDLTerm.class.equals(BasicSnippetData.Key.LOOP_INVARIANT_TERM.getType());
        JavaDLTerm origLoopInv = (JavaDLTerm) d.get(
                BasicSnippetData.Key.LOOP_INVARIANT_TERM);
        return replace(origLoopInv, d.origVars, poVars.pre, d.tb);
    }

}