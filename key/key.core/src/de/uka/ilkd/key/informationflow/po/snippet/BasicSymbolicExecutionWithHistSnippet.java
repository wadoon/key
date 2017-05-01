package de.uka.ilkd.key.informationflow.po.snippet;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.dependencycluster.po.SymbExecWithHistFactory;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicSymbolicExecutionWithHistSnippet
        extends BasicSymbolicExecutionSnippet {

    public Term produce(BasicSnippetData d, ProofObligationVars poVars,
            SymbExecWithHistFactory helperFactory) {
        assert poVars.exceptionParameter.op() instanceof LocationVariable :
            "Something is wrong with the catch variable";

        ImmutableList<Term> posts = ImmutableSLList.<Term>nil();
        if (poVars.post.self != null) {
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));
        }
        

        if (poVars.post.result != null) {
            posts = posts.append(d.tb.equals(poVars.post.result,
                    poVars.pre.result));
        }

        posts = posts.append(d.tb.equals(poVars.post.exception,
                poVars.pre.exception));
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));
        
        posts = posts.append(helperFactory.postHistoryEquality());
        
        final Term prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }

}
