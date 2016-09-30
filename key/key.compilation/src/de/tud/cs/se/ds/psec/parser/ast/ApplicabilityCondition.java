package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;
import java.util.function.Function;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * A condition on the applicability of a translation.
 *
 * @author Dominic Scheurer
 */
public class ApplicabilityCondition extends TranslationTacletASTElement {

    private Function<ApplicabilityCheckInput, Boolean> applicabilityCheck;

    /**
     * @param applicabilityCheck
     *            A function for checking whether certain fine-grained
     *            constraints are met which are required for using this
     *            {@link TranslationDefinition} for translating a given element
     *            in the symbolic execution taclet AST.
     */
    public ApplicabilityCondition(
            Function<ApplicabilityCheckInput, Boolean> applicabilityCheck) {
        this.applicabilityCheck = applicabilityCheck;
    }

    /**
     * Checks whether this {@link ApplicabilityCondition} is met under the
     * supplied {@link ApplicabilityCheckInput}.
     * 
     * @param input
     *            The necessary information for doing the applicability check.
     * @return true iff all constraints are met.
     */
    public boolean isApplicable(ApplicabilityCheckInput input) {
        return applicabilityCheck.apply(input);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, TacletApp app, List<TacletASTNode> children) {
        // This element should not be translated.
        // That's maybe a design flaw...
    }

}
