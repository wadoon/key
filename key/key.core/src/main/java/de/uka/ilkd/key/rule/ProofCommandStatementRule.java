package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.merge.MergeRule;
import org.key_project.util.collection.ImmutableList;

/**
 * @author Alexander Weigl
 * @version 1 (11/16/20)
 */
public class ProofCommandStatementRule implements BuiltInRule {
    public static final ProofCommandStatementRule INSTANCE = new ProofCommandStatementRule();
    private static final String DISPLAY_NAME = "Apply command";
    private static final Name NAME = new Name("apply_embedded_proof_command");


    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        Term term = pio.subTerm();
        //check for proof command statement
        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return null;
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        return null;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }
}
