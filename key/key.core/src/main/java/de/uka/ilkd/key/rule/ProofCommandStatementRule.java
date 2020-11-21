package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.ProofCommandStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NodeInfo;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;

import java.util.List;

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
        SourceElement activeStatement = getProofCommand(pio);
        if (activeStatement == null) return false;
        if (activeStatement instanceof ProofCommandStatement) {
            ProofCommandStatement cmd = (ProofCommandStatement) activeStatement;
            String name = cmd.getCommand();
            switch (name.trim()) {
                case "ignore":
                    return true;
            }

        }
        return false;
    }

    @Nullable
    private SourceElement getProofCommand(PosInOccurrence pio) {
        final Term term = pio.subTerm();
        if (term == null) return null;
        final JavaBlock javaBlock = term.javaBlock();
        if (javaBlock == null) return null;

        @Nullable SourceElement activeStatement = NodeInfo.computeActiveStatement(javaBlock.program().getFirstElement());
        return activeStatement;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new IBuiltInRuleApp() {
            @Override
            public BuiltInRule rule() {
                return ProofCommandStatementRule.INSTANCE;
            }

            @Override
            public IBuiltInRuleApp tryToInstantiate(Goal goal) {
                return null;
            }

            @Override
            public IBuiltInRuleApp forceInstantiate(Goal goal) {
                return null;
            }

            @Override
            public List<LocationVariable> getHeapContext() {
                return null;
            }

            @Override
            public boolean isSufficientlyComplete() {
                return false;
            }

            @Override
            public ImmutableList<PosInOccurrence> ifInsts() {
                return null;
            }

            @Override
            public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
                return null;
            }

            @Override
            public IBuiltInRuleApp replacePos(PosInOccurrence newPos) {
                return null;
            }

            @Override
            public PosInOccurrence posInOccurrence() {
                return pos;
            }

            @Override
            public ImmutableList<Goal> execute(Goal goal, Services services) {
                return ProofCommandStatementRule.this.apply(goal, services, this);
            }

            @Override
            public boolean complete() {
                return true;
            }
        };
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)  {
        goal.node().getNodeInfo().setInteractiveRuleApplication(true);
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
