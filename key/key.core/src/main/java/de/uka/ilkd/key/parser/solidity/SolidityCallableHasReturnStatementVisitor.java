package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.tree.TerminalNode;

/**
 * This visitor is used to check whether a function/constructor/modifier body contains a return statement.
 */
public class SolidityCallableHasReturnStatementVisitor extends SolidityBaseVisitor<Boolean> {
    @Override public Boolean visitReturnStatement(SolidityParser.ReturnStatementContext ctx) {
        return true;
    }

    @Override public Boolean visitBlock(SolidityParser.BlockContext ctx) {
        if (ctx.statement() == null || ctx.statement().isEmpty()) {
            return false;
        }
        for (SolidityParser.StatementContext stmntCtx : ctx.statement()) {
            if (visit(stmntCtx))
                return true;
        }
        return false;
    }

    @Override public Boolean visitTerminal(TerminalNode n) { return false; }
}