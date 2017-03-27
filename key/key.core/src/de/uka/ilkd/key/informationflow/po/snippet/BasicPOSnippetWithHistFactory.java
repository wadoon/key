package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory.Snippet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicPOSnippetWithHistFactory extends BasicPOSnippetFactoryImpl {
    private final SymbExecWithHistFactory helperFactory;

    BasicPOSnippetWithHistFactory(BasicSnippetData data, ProofObligationVars poVars, SymbExecWithHistFactory helperFactory) {
        super(data, poVars);
        this.helperFactory = helperFactory;
    }
    
    @Override
    public Term create(Snippet snippet) throws UnsupportedOperationException {
        Term result;
        try {         
            switch (snippet) {
                case SYMBOLIC_EXEC: 
                    result = new BasicSymbolicExecutionWithHistSnippet().produce(data, poVars, helperFactory);
                    break;
                default:
                    FactoryMethod m = factoryMethods.get(snippet);                    
                    if (m == null) {
                        throw new UnsupportedOperationException("Unknown factory "
                                + "method for snippet \"" + snippet.name() + ".");
                    }
                    result = m.produce(data, poVars);
                    break;
            }
            return result;
        } catch (TermCreationException e) {
            throw new UnsupportedOperationException("Factory method for "
                    + "snippet \"" + snippet.name() + " threw "
                    + "TermCreationException: " + e.getMessage(), e);
        }
    }
}
