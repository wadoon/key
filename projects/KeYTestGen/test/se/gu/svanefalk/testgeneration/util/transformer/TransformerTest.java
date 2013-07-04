package se.gu.svanefalk.testgeneration.util.transformer;

import java.io.IOException;

import junit.framework.Assert;

import org.junit.Test;

import se.gu.svanefalk.testgeneration.core.keyinterface.KeYInterfaceException;
import se.gu.svanefalk.testgeneration.util.TermEquivalenceChecker;
import se.gu.svanefalk.testgeneration.util.UtilTest;
import se.gu.svanefalk.testgeneration.util.transformers.ITermTransformer;
import se.gu.svanefalk.testgeneration.util.transformers.TermTransformerException;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

public class TransformerTest extends UtilTest {

    private final TermEquivalenceChecker termEquivalenceChecker = TermEquivalenceChecker.getInstance();
    protected ITermTransformer transformer;
    TermFactory termFactory = TermFactory.DEFAULT;

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
    public void testTransformIntegerComparisons() throws ProofInputException,
            TermTransformerException {

        IExecutionNode targetNode = getFirstSymbolicNodeForStatement("max",
                "return a");

        Term originalTerm = targetNode.getPathCondition();
        // Artificially impose an external negation
        originalTerm = termFactory.createTerm(Junctor.NOT, originalTerm);

        // Remove the external negation
        Term transformedTerm = transformer.transform(originalTerm);

        Assert.assertTrue(areEquivalent(originalTerm, transformedTerm));
    }

    @Test
    public void testTransformIntegerComparisons2() throws ProofInputException,
            TermTransformerException {

        IExecutionNode targetNode = getFirstSymbolicNodeForStatement("max",
                "return b");

        Term originalTerm = targetNode.getPathCondition();
        // Artificially impose an external negation
        originalTerm = termFactory.createTerm(Junctor.NOT, originalTerm);

        // Remove the external negation
        Term transformedTerm = transformer.transform(originalTerm);

        Assert.assertTrue(areEquivalent(originalTerm, transformedTerm));
    }

    @Test
    public void testTransformMixedComparisons() throws ProofInputException,
            TermTransformerException {

        IExecutionNode targetNode = getFirstSymbolicNodeForStatement(
                "midOneProxyOneInstance", "mid=x");

        Term originalTerm = targetNode.getPathCondition();
        // Artificially impose an external negation
        originalTerm = termFactory.createTerm(Junctor.NOT, originalTerm);

        // Remove the external negation
        Term transformedTerm = transformer.transform(originalTerm);

        Assert.assertTrue(areEquivalent(originalTerm, transformedTerm));
    }
}
