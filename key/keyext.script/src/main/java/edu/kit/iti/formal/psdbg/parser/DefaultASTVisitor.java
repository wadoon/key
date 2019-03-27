package edu.kit.iti.formal.psdbg.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */
import edu.kit.iti.formal.psdbg.parser.ast.*;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class DefaultASTVisitor<T> implements Visitor<T> {
    public T defaultVisit(ASTNode node) {
        return null;
    }

    @Override
    public T visit(ProofScript proofScript) {
        return defaultVisit(proofScript);
    }

    @Override
    public T visit(AssignmentStatement assignment) {
        return defaultVisit(assignment);
    }

    @Override
    public T visit(BinaryExpression binaryExpression) {
        return defaultVisit(binaryExpression);
    }

    @Override
    public T visit(MatchExpression matchExpression) {
        return defaultVisit(matchExpression);
    }

    @Override
    public T visit(TermLiteral termLiteral) {
        return defaultVisit(termLiteral);
    }

    @Override
    public T visit(StringLiteral stringLiteral) {
        return defaultVisit(stringLiteral);
    }

    @Override
    public T visit(Variable variable) {
        return defaultVisit(variable);
    }

    @Override
    public T visit(BooleanLiteral booleanLiteral) {
        return defaultVisit(booleanLiteral);
    }

    @Override
    public T visit(Statements statements) {
        return defaultVisit(statements);
    }

    @Override
    public T visit(IntegerLiteral integer) {
        return defaultVisit(integer);
    }

    @Override
    public T visit(CasesStatement casesStatement) {
        return defaultVisit(casesStatement);
    }

    @Override
    public T visit(DefaultCaseStatement defCase) {
        return defaultVisit(defCase);
    }

    @Override
    public T visit(CaseStatement caseStatement) {
        return defaultVisit(caseStatement);
    }

    @Override
    public T visit(SubstituteExpression subst) {
        return defaultVisit(subst);
    }

    @Override
    public T visit(CallStatement call) {
        return defaultVisit(call);
    }

    @Override
    public T visit(TheOnlyStatement theOnly) {
        return defaultVisit(theOnly);
    }

    @Override
    public T visit(ForeachStatement foreach) {
        return defaultVisit(foreach);
    }

    @Override
    public T visit(RepeatStatement repeatStatement) {
        return defaultVisit(repeatStatement);
    }

    @Override
    public T visit(Signature signature) {
        return defaultVisit(signature);
    }

    @Override
    public T visit(Parameters parameters) {
        return defaultVisit(parameters);
    }

    @Override
    public T visit(UnaryExpression unaryExpression) {
        return defaultVisit(unaryExpression);
    }

    @Override
    public T visit(TryCase TryCase) {
        return defaultVisit(TryCase);
    }

    @Override
    public T visit(GuardedCaseStatement guardedCaseStatement) {
        return defaultVisit(guardedCaseStatement);
    }

    @Override
    public T visit(ClosesCase closesCase) {
        return defaultVisit(closesCase);
    }

    @Override
    public T visit(FunctionCall func) {
        return defaultVisit(func);
    }

    @Override
    public T visit(WhileStatement ws) {
        return defaultVisit(ws);
    }

    @Override
    public T visit(IfStatement is) {
        return defaultVisit(is);
    }

    @Override
    public T visit(StrictBlock strictBlock) {
        return defaultVisit(strictBlock);
    }

    @Override
    public T visit(RelaxBlock relaxBlock) {
        return defaultVisit(relaxBlock);
    }

    @Override
    public T visit(LetStatement let) {
        return defaultVisit(let);
    }
}

