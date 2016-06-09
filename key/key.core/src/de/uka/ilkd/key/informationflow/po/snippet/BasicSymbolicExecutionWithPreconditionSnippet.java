package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


/**
 *
 * @author christoph
 */
class BasicSymbolicExecutionWithPreconditionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(d, poVars);

        // precondition
        final JavaDLTerm freePre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final JavaDLTerm contractPre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        final JavaDLTerm pre = d.tb.and(freePre, contractPre);

        // symbolic execution
        final JavaDLTerm symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC);

        // final symbolic execution term
        return d.tb.and(pre, symExec);
    }

}