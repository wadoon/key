package edu.kit.iti.formal.psdbg.lint.checkers;

import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import edu.kit.iti.formal.psdbg.parser.types.Type;
import org.antlr.v4.runtime.Token;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
public class VariableDeclarationCheck extends AbstractLintRule {
    private static final Issue REDECLARE_VARIABLE = Issue.REDECLARE_VARIABLE;
    private static final Issue REDECLARE_VARIABLE_TYPE_MISMATCH = Issue.REDECLARE_VARIABLE_TYPE_MISMATCH;
    private static final Issue VARIABLE_NOT_DECLARED = Issue.VARIABLE_NOT_DECLARED;
    private static final Issue VARIABLE_NOT_USED = Issue.VARIABLE_NOT_USED;

    public VariableDeclarationCheck() {
        super(UVSearcher::new);
    }

    static class UVSearcher extends Searcher {
        private VariableAssignment current = new VariableAssignment(null);
        private Map<String, Token> hits = new HashMap<>();


        @Override
        public Void visit(ProofScript proofScript) {
            current = current.push();
            super.visit(proofScript);
            current = current.pop();
            current.asMap().forEach((s, t) -> {
                if (hits.get(s) != null) {
                    problem(VARIABLE_NOT_USED);
                }
            });

            return null;
        }

        @Override
        public Void visit(TheOnlyStatement foreach) {
            current = current.push();
            super.visit(foreach);
            current = current.pop();
            return null;
        }

        @Override
        public Void visit(CaseStatement caseStatement) {
            current = current.push();
            super.visit(caseStatement);
            current = current.pop();
            return null;
        }

        @Override
        public Void visit(SubstituteExpression subst) {
            return null;
        }

        @Override
        public Void visit(FunctionCall func) {
            return null;
        }

        private void declare(Variable var, Type type) {
            if (current.getType(var) != null) {
                problem(REDECLARE_VARIABLE).tokens(var.getToken());

                if (!current.getType(var).equals(type)) {
                    problem(REDECLARE_VARIABLE_TYPE_MISMATCH).tokens(var.getToken());
                }
            } else {
                current.declare(var, type);
            }
        }

        private void check(Variable var) {
            if (!current.getTypes().containsKey(var.getIdentifier())) {
                problem(VARIABLE_NOT_DECLARED).tokens(var.getToken());
            }
            hits.put(var.getIdentifier(), var.getToken());
        }

        @Override
        public Void visit(Signature signature) {
            for (Map.Entry<Variable, Type> v : signature.entrySet()) {
                declare(v.getKey(), v.getValue());
            }
            return null;
        }

        @Override
        public Void visit(AssignmentStatement assign) {
            if (assign.getRhs() != null)
                assign.getRhs().accept(this);

            if (assign.getType() != null) {
                declare(assign.getLhs(), assign.getType());
            } else {
                check(assign.getLhs());
            }

            return null;
        }


        @Override
        public Void visit(Variable v) {
            check(v);
            return null;
        }

        @Override
        public Void visit(Parameters parameters) {
            for (Expression e : parameters.values()) {
                e.accept(this);
            }
            return null;
        }

    }
}
