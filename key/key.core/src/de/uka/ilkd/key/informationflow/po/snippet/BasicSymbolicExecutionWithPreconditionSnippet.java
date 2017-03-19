package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.po.snippet.BasicSnippetData.Key;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


/**
 *
 * @author christoph
 */
class BasicSymbolicExecutionWithPreconditionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(d, poVars);

        // precondition
        final Term freePre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        
        
        
        //TODO JK put this somewhere else to not break christoph's  NI stuff
        //final Term event = d.tb.func(eventFunction, calltype, callDirection, d.origVars.self, d.get(Key.TARGET_METHOD), d.tb.seq(poVars.formalParams), poVars.pre.heap)
        //final Term actualHistory = d.tb.select(asSort, h, o, f);
        //final Term historyWithCallEvent = d.tb.seqSingleton(event);
        //final Term initHistory = d.tb.equals(actualHistory, historyWithCallEvent);
        
        
        
        
        final Term pre = d.tb.and(freePre, contractPre);

        // symbolic execution
        final Term symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC);

        // final symbolic execution term
        return d.tb.and(pre, symExec);
    }

}