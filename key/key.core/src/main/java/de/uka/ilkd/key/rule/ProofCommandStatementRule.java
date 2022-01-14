package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.ProofCommandStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.NodeInfo;
import org.key_project.util.collection.ImmutableList;

import javax.annotation.Nullable;

/**
 * This should better be a taclet eventually which just treats the proof command
 * statement as a NOP.
 *
 * @author Alexander Weigl, Mattias Ulbrich
 * @version 1 (11/16/20)
 */
public class ProofCommandStatementRule implements BuiltInRule {
    public static final ProofCommandStatementRule INSTANCE = new ProofCommandStatementRule();
    private static final String DISPLAY_NAME = "Apply command";
    private static final Name NAME = new Name("apply_embedded_proof_command");

    public static ProofCommandStatement getCommand(PosInOccurrence pio) {
        SourceElement act = getActiveStatement(pio);
        if (act instanceof ProofCommandStatement) {
            return (ProofCommandStatement) act;
        }
        throw new IllegalArgumentException("Unexpected pio: " + pio);
    }


    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        SourceElement activeStatement = getActiveStatement(pio);
        if (activeStatement == null) return false;
        if (activeStatement instanceof ProofCommandStatement) {
            return true;
        }
        return false;
    }

    @Nullable
    private static SourceElement getActiveStatement(PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel()) {
            return null;
        }
        Term term = pio.subTerm();
        if (term == null) {
            return null;
        }
        if(term.op() == UpdateApplication.UPDATE_APPLICATION) {
            term = term.sub(1);
        }
        final JavaBlock javaBlock = term.javaBlock();
        if (javaBlock == null) {
            return null;
        }

        return NodeInfo.computeActiveStatement(javaBlock.program().getFirstElement());
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return true;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)  {
        TermBuilder tb = services.getTermBuilder();
        PosInOccurrence pio = ruleApp.posInOccurrence();
        assert pio.isTopLevel();
        Term term = pio.subTerm();
        Term upd = null;
        if (term.op() == UpdateApplication.UPDATE_APPLICATION) {
            upd = term.sub(0);
            term = term.sub(1);
        }
        JavaBlock jb = term.javaBlock();
        StatementBlock block = UseOperationContractRule.replaceStatement(jb, new StatementBlock());
        JavaBlock newJB = JavaBlock.createJavaBlock(block);
        Term newTerm = tb.prog((Modality) term.op(), newJB, term.sub(0));
        if (upd != null) {
            newTerm = tb.apply(upd, newTerm);
        }
        ImmutableList<Goal> result = goal.split(1);
        result.head().changeFormula(new SequentFormula(newTerm), pio);
        return result;
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
