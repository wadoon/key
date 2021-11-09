package de.uka.ilkd.key.smt.quant_inst;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.SMTProofBaseVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;
import de.uka.ilkd.key.smt.proofrules.QuantInst;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

public class QuantInstExtractor extends SMTProofBaseVisitor<Void> {

    private final QuantInstExploiter exploiter;
    private final Goal goal;
    private final Services services;

    public QuantInstExtractor(QuantInstExploiter exploiter, Goal goal) {
        this.exploiter = exploiter;
        this.goal = goal;
        services = goal.proof().getServices();
    }

    @Override
    public Void visitProofsexpr(SMTProofParser.ProofsexprContext ctx) {

        // do not descend into let terms
        if (ctx.LET() != null) {
            return null;
        }

        Token rule = ctx.rulename;
        if (rule == null) {
            return super.visitProofsexpr(ctx);
        }

        String rulename = ctx.rulename.getText();
        if (rulename.equals("quant-inst")) {

            // Z3 quant-inst may perform multiple instantiations at once
            int instVarCount = QuantInst.extractInstVarCount(ctx, exploiter);

            for (int i = 0; i < instVarCount; i++) {
                Term inst = QuantInst.extractQuantifierInstantiation(ctx, i, exploiter, services);
                exploiter.addInstantiation(inst);
            }
            return null;
        }

        return super.visitProofsexpr(ctx);
    }
}
