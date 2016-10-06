package de.tud.cs.se.ds.psec.parser.ast;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * The definition of a translation. A translation is applicable if
 * <ol>
 * <li>The symbolic execution taclet to be translated is contained in the list
 * returned by {@link #getSymbExTacletReferences()}</li>
 * <li>The method {@link #isApplicable(ApplicabilityCheckInput)} returns true
 * for the given {@link ApplicabilityCheckInput} describing the situation.</li>
 * </ol>
 * 
 * If all constraints are met, call
 * {@link #translate(MethodVisitor, ProgVarHelper, UniqueLabelManager, TacletApp, List)}
 * to start the translation.
 *
 * @author Dominic Scheurer
 */
public class TranslationDefinition extends TranslationTacletASTElement {

    private ArrayList<String> symbExTacletReferences;
    private Function<ApplicabilityCheckInput, Boolean> applicabilityCheck;
    private Instructions instructions;

    /**
     * @param symbExTacletReferences
     *            The symbolic execution taclets that this
     *            {@link TranslationDefinition} can translate.
     * @param applicabilityCheck
     *            A function for checking whether certain fine-grained
     *            constraints are met which are required for using this
     *            {@link TranslationDefinition} for translating a given element
     *            in the symbolic execution taclet AST.
     * @param instructions
     *            The {@link Instructions} object for translation.
     */
    public TranslationDefinition(ArrayList<String> symbExTacletReferences,
            Function<ApplicabilityCheckInput, Boolean> applicabilityCheck,
            Instructions instructions) {
        this.symbExTacletReferences = symbExTacletReferences;
        this.applicabilityCheck = applicabilityCheck;
        this.instructions = instructions;
    }

    /**
     * @return The symbolic execution taclets that this
     *         {@link TranslationDefinition} can translate.
     */
    public ArrayList<String> getSymbExTacletReferences() {
        return symbExTacletReferences;
    }

    /**
     * Checks whether this {@link TranslationDefinition} is applicable under the
     * conditions given by the {@link ApplicabilityCheckInput}. This already
     * assumes that the symbolic execution taclet that is to be translated is
     * contained in {@link #getSymbExTacletReferences()}.
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
            UniqueLabelManager labelManager, TacletApp app, Services services,
            List<TacletASTNode> children) {
        instructions.translate(mv, pvHelper, labelManager, app, services,
                children);
    }

    /**
     * Computes the number of children calls as defined in the
     * {@link TranslationDefinition}. This may be used to ignore branches in the
     * SET that should be ignored according to the translation.
     * 
     * @return The number of children calls in this
     *         {@link TranslationDefinition}.
     */
    public int numberOfChildrenCalls() {
        return instructions.numberOfChildrenCalls();
    }

}
