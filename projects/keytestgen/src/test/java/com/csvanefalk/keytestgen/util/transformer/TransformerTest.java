package com.csvanefalk.keytestgen.util.transformer;

import com.csvanefalk.keytestgen.core.keyinterface.KeYInterfaceException;
import com.csvanefalk.keytestgen.util.TermEquivalenceChecker;
import com.csvanefalk.keytestgen.util.UtilTest;
import com.csvanefalk.keytestgen.util.transformers.ITermTransformer;
import com.csvanefalk.keytestgen.util.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import junit.framework.Assert;
import org.junit.Test;

import java.io.IOException;

public class TransformerTest extends UtilTest {

    private final TermEquivalenceChecker termEquivalenceChecker = TermEquivalenceChecker.getInstance();
    protected ITermTransformer transformer;
    TermFactory termFactory = new TermFactory();

    public TransformerTest() throws KeYInterfaceException, IOException {
        super("own");
        transformer = new ITermTransformer() {

            @Override
            public Term transform(Term term) throws TermTransformerException {
                return term;
            }
        };
    }

    protected boolean areEquivalent(Term firstTerm, Term secondTerm) {
        return termEquivalenceChecker.areEquivalent(firstTerm, secondTerm);
    }

    @Test
    public void testTransformIntegerComparisons() throws ProofInputException, TermTransformerException {

        IExecutionNode targetNode = getFirstSymbolicNodeForStatement("max", "return a");

        Term originalTerm = targetNode.getPathCondition();
        // Artificially impose an external negation
        originalTerm = termFactory.createTerm(Junctor.NOT, originalTerm);

        // Remove the external negation
        Term transformedTerm = transformer.transform(originalTerm);

        Assert.assertTrue(areEquivalent(originalTerm, transformedTerm));
    }

    @Test
    public void testTransformIntegerComparisons2() throws ProofInputException, TermTransformerException {

        IExecutionNode targetNode = getFirstSymbolicNodeForStatement("max", "return b");

        Term originalTerm = targetNode.getPathCondition();
        // Artificially impose an external negation
        originalTerm = termFactory.createTerm(Junctor.NOT, originalTerm);

        // Remove the external negation
        Term transformedTerm = transformer.transform(originalTerm);

        Assert.assertTrue(areEquivalent(originalTerm, transformedTerm));
    }

    @Test
    public void testTransformMixedComparisons() throws ProofInputException, TermTransformerException {

        IExecutionNode targetNode = getFirstSymbolicNodeForStatement("midOneProxyOneInstance", "mid=x");

        Term originalTerm = targetNode.getPathCondition();
        // Artificially impose an external negation
        originalTerm = termFactory.createTerm(Junctor.NOT, originalTerm);

        // Remove the external negation
        Term transformedTerm = transformer.transform(originalTerm);

        Assert.assertTrue(areEquivalent(originalTerm, transformedTerm));
    }
}
