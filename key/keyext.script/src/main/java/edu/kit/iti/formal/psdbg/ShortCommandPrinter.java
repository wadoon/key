package edu.kit.iti.formal.psdbg;

import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.Facade;
import edu.kit.iti.formal.psdbg.parser.ast.*;

/**
 * Prints every command to a single line representation.
 *
 * @author Alexander Weigl
 * @version 1
 */
public class ShortCommandPrinter extends DefaultASTVisitor<String> {
    @Override
    public String defaultVisit(ASTNode node) {
        return (Facade.prettyPrint(node));
    }

    @Override
    public String visit(Statements statements) {
        return "{ ... " + statements.size() + " ... }";
    }

    @Override
    public String visit(ProofScript proofScript) {
        return String.format("script %s (%s) {%n",
                proofScript.getName(),
                Facade.prettyPrint(proofScript.getSignature()));
    }

    @Override
    public String visit(CasesStatement casesStatement) {
        return "cases {";
    }

    @Override
    public String visit(GuardedCaseStatement caseStatement) {
        return "case " + Facade.prettyPrint(caseStatement.getGuard());
    }

    @Override
    public String visit(TryCase tryCase) {
        return "try " + Facade.prettyPrint(tryCase.getBody());
    }

    @Override
    public String visit(ClosesCase closesCase) {
        return "closes with {" + Facade.prettyPrint(closesCase.getClosesGuard()) + "}";
    }

    @Override
    public String visit(TheOnlyStatement theOnly) {
        return "theonly {";
    }

    @Override
    public String visit(ForeachStatement foreach) {
        return "foreach {";
    }

    @Override
    public String visit(RepeatStatement repeatStatement) {
        return ("repeat {");
    }
}
