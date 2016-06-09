package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


public class InfFlowLoopInvAppSnippet extends ReplaceAndRegisterMethod
        implements InfFlowFactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars1,
                        ProofObligationVars poVars2) throws UnsupportedOperationException {
        BasicPOSnippetFactory f1 =
                POSnippetFactory.getBasicFactory(d, poVars1);
        BasicPOSnippetFactory f2 =
                POSnippetFactory.getBasicFactory(d, poVars2);

        JavaDLTerm loopInv1 = f1.create(BasicPOSnippetFactory.Snippet.LOOP_INV);
        JavaDLTerm loopInv2 = f2.create(BasicPOSnippetFactory.Snippet.LOOP_INV);


        InfFlowPOSnippetFactory iff =
                POSnippetFactory.getInfFlowFactory(d, poVars1, poVars2);
        JavaDLTerm inOutRelations =
                iff.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APP_INOUT_RELATION);
        return d.tb.imp(d.tb.and(loopInv1, loopInv2), inOutRelations);
    }
}