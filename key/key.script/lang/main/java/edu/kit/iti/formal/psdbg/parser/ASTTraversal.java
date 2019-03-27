package edu.kit.iti.formal.psdbg.parser;

        /*-
         * #%L
         * ProofScriptParser
         * %%
         * Copyright (C) 2017 Application-oriented Formal Verification
         * %%
         * This program is free software: you can redistribute it and/or modify
         * it under the terms of the GNU General default License as
         * published by the Free Software Foundation, either version 3 of the
         * License, or (at your option) any later version.
         *
         * This program is distributed in the hope that it will be useful,
         * but WITHOUT ANY WARRANTY; without even the implied warranty of
         * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
         * GNU General default License for more details.
         *
         * You should have received a copy of the GNU General default
         * License along with this program.  If not, see
         * <http://www.gnu.org/licenses/gpl-3.0.html>.
         * #L%
         */


import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.types.Type;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * {@link ASTTraversal} provides a visitor with a a default traversal of the given AST.
 *
 * @author Alexander Weigl
 * @version 1 (29.04.17)
 */
public interface ASTTraversal<T> extends Visitor<T> {

    default Stream<T> allOf(Stream<ASTNode> nodes) {
        return nodes.map(n -> (T) n.accept(this));
    }

    default List<T> allOf(Collection<ASTNode> nodes) {
        if (nodes.size() == 0) return Collections.emptyList();
        return allOf(nodes.stream()).collect(Collectors.toList());
    }

    default Stream<T> allOf(ASTNode... nodes) {
        if (nodes.length == 0) return (Stream<T>) Collections.emptyList().stream();
        return allOf(Arrays.stream(nodes));
    }

    default T oneOf(Stream<? extends ASTNode> nodes) {
        return (T) nodes
                .filter(Objects::nonNull)
                .map(n -> (T) n.accept(this))
                .filter(Objects::nonNull)
                .findFirst()
                .orElse((T) null);
    }

    default T oneOf(ASTNode... nodes) {
        if (nodes.length == 0) return null;
        return oneOf(Arrays.stream(nodes));
    }

    default T oneOf(Collection<ASTNode> nodes) {
        if (nodes.size() == 0) return null;
        return oneOf(nodes.stream());
    }


    @Override
    default T visit(ProofScript proofScript) {
        proofScript.getSignature().accept(this);
        proofScript.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(AssignmentStatement assign) {
        assign.getLhs().accept(this);
        return null;
    }

    @Override
    default T visit(BinaryExpression e) {
        e.getLeft().accept(this);
        e.getRight().accept(this);
        return null;
    }

    @Override
    default T visit(MatchExpression match) {
        match.getPattern().accept(this);
        return null;
    }

    @Override
    default T visit(TermLiteral term) {
        return null;
    }

    @Override
    default T visit(StringLiteral string) {
        return null;
    }

    @Override
    default T visit(Variable variable) {
        return null;
    }

    @Override
    default T visit(BooleanLiteral bool) {
        return null;
    }

    @Override
    default T visit(Statements statements) {
        for (Statement statement : statements) {
            statement.accept(this);
        }
        return null;
    }

    @Override
    default T visit(IntegerLiteral integer) {
        return null;
    }

    @Override
    default T visit(CasesStatement casesStatement) {
        for (CaseStatement c : casesStatement.getCases()) {
            c.accept(this);
        }
        return null;
    }

    @Override
    default T visit(CaseStatement caseStatement) {
        //caseStatement.getBody().accept(this);
        caseStatement.accept(this);
        return null;
    }

    @Override
    default T visit(CallStatement call) {
        for (Expression e : call.getParameters().values()) {
            e.accept(this);
        }
        return null;
    }

    @Override
    default T visit(TheOnlyStatement theOnly) {
        theOnly.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(ForeachStatement foreach) {
        foreach.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(RepeatStatement repeatStatement) {
        repeatStatement.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(Signature signature) {
        for (Map.Entry<Variable, Type> e : signature.entrySet()) {
            e.getKey().accept(this);
        }
        return null;
    }

    @Override
    default T visit(Parameters parameters) {
        for (Map.Entry<Variable, Expression> e :
                parameters.entrySet()) {
            e.getKey().accept(this);
            e.getValue().accept(this);
        }
        return null;
    }

    @Override
    default T visit(UnaryExpression e) {
        e.getExpression().accept(this);
        return null;
    }

    @Override
    default T visit(TryCase TryCase) {
        TryCase.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(GuardedCaseStatement guardedCaseStatement) {
        guardedCaseStatement.getGuard().accept(this);
        guardedCaseStatement.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(SubstituteExpression subst) {
        subst.getSub().accept(this);
        for (Expression e : subst.getSubstitution().values()) {
            e.accept(this);
        }
        return null;
    }

    @Override
    default T visit(ClosesCase closesCase) {
        closesCase.getClosesGuard().accept(this);
        closesCase.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(DefaultCaseStatement defCase) {
        defCase.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(FunctionCall func) {
        func.getArguments().forEach(a -> a.accept(this));
        return null;
    }

    @Override
    default T visit(WhileStatement ws) {
        ws.getCondition().accept(this);
        ws.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(IfStatement is) {
        is.getCondition().accept(this);
        is.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(StrictBlock strictBlock) {
        strictBlock.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(RelaxBlock relaxBlock) {
        relaxBlock.getBody().accept(this);
        return null;
    }

    @Override
    default T visit(LetStatement let) {
        let.getExpression().accept(this);
        let.getBody().accept(this);
        return null;
    }
}
