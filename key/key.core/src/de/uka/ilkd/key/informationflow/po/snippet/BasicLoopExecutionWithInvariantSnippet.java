package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


/**
 *
 * @author christoph
 */
class BasicLoopExecutionWithInvariantSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(d, poVars);

        // loop invariant
        final JavaDLTerm freeInv =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_INV);
        final JavaDLTerm loopInv =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_INV);
        final JavaDLTerm inv = d.tb.and(freeInv, loopInv);

        // symbolic execution
        JavaDLTerm symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_EXEC);


        // final symbolic execution term
        return d.tb.and(inv, symExec);
    }

}