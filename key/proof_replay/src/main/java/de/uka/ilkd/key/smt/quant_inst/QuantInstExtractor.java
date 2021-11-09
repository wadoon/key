package de.uka.ilkd.key.smt.quant_inst;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.CloseByReferenceRule;
import de.uka.ilkd.key.smt.SMTProofBaseVisitor;
import de.uka.ilkd.key.smt.SMTProofParser;
import de.uka.ilkd.key.smt.proofrules.QuantInst;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.List;

import static de.uka.ilkd.key.rule.CloseByReferenceRule.INSTANCE;

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

        Token rule = ctx.rulename;
        if (rule == null) {
            return super.visitProofsexpr(ctx);
        }

        String rulename = ctx.rulename.getText();
        if (rulename.equals("quant-inst")) {

            // ctx is: (or (not (forall (x) (P x))) (P a))

            /* since we use the complete instantiated term (P a), we do not need this anymore:
            // Z3 quant-inst may perform multiple instantiations at once
            int instVarCount = QuantInst.extractInstVarCount(ctx, exploiter);

            for (int i = 0; i < instVarCount; i++) {
                Term inst = QuantInst.extractQuantifierInstantiation(ctx, i, exploiter, services);
                exploiter.addInstantiation(inst);
            }*/

            Term instantiated = QuantInst.extractQuantifierInstantiation(ctx, exploiter, services);
            exploiter.addInstantiation(instantiated);
            return null;
        }

        return super.visitProofsexpr(ctx);
    }

    @Override
    public Void visitIdentifier(SMTProofParser.IdentifierContext ctx) {
        ParserRuleContext def = exploiter.getSymbolDef(ctx.getText(), ctx);
        if (def != null) {
            // continue searching for instantiations in the partial tree from the symbol table
            visit(def);
        }
        return null;
    }
}
