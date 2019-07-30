package org.key_project.script.ui;

import edu.kit.iti.formal.psdbg.interpreter.exceptions.NoCallHandlerException;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.CommandHandler;
import edu.kit.iti.formal.psdbg.interpreter.funchdl.DefaultLookup;
import edu.kit.iti.formal.psdbg.lint.Issue;
import edu.kit.iti.formal.psdbg.lint.Level;
import edu.kit.iti.formal.psdbg.lint.LintProblem;
import edu.kit.iti.formal.psdbg.lint.checkers.AbstractLintRule;
import edu.kit.iti.formal.psdbg.lint.checkers.Searcher;
import edu.kit.iti.formal.psdbg.lint.checkers.SearcherFactory;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import edu.kit.iti.formal.psdbg.parser.ast.CallStatement;
import edu.kit.iti.formal.psdbg.parser.ast.ProofScript;
import edu.kit.iti.formal.psdbg.parser.ast.Statements;
import lombok.AllArgsConstructor;
import org.antlr.v4.runtime.Token;
import org.fife.ui.autocomplete.AutoCompletion;
import org.fife.ui.autocomplete.Completion;
import org.fife.ui.autocomplete.CompletionProvider;
import org.fife.ui.autocomplete.CompletionProviderBase;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl, S.Grebing
 * @version 1 (26.07.19)
 */
public class CallLinter extends AbstractLintRule {
    @Override
    public void check(List<? extends ASTNode> node, List<LintProblem> problems) {
        super.check(node, problems);

    }

    private final DefaultLookup lookup;

    protected CallLinter(DefaultLookup lookup) {
        super(new CallLintSearcher(lookup));
        this.lookup = lookup;

    }



    public String getName() {
        return getClass().getSimpleName();
    }

    private static class CallLintSearcher implements SearcherFactory {
        DefaultLookup lookup;
        public CallLintSearcher(DefaultLookup lookup) {
            this.lookup = lookup;
        }

        @Override
        public Searcher create() {
            return new CallLintVisitor(lookup);
        }

        private class CallLintVisitor extends Searcher {
            DefaultLookup lookup;
            public CallLintVisitor(DefaultLookup lookup) {
                super();
                this.lookup = lookup;
            }

            @Override
            public Void visit(ProofScript proofScript) {
                return super.visit(proofScript);
            }

            @Override
            public Void visit(Statements statements) {
                return super.visit(statements);
            }

            @Override
            public Void visit(CallStatement call) {

                try {
                    lookup.getBuilder(call, null);
                } catch (NoCallHandlerException nce) {
                    List<String> commands = new ArrayList<>();

                    List<CommandHandler> builders = lookup.getBuilders();
                    builders.forEach(builder -> {
                        commands.addAll(builder.getAllCommandStrings());
                    });

                    AutoCompletion autoCompletion = ScriptUtils.createAutoCompletion();

                    List<Completion> completions = autoCompletion.getCompletionProvider().getCompletions(new JTextField(call.getCommand()));
                    completions.forEach(completion -> System.out.println("completion = " + completion));
                    Issue callUndefined = Issue.CALL_UNDEFINED;

                    System.out.println("Could not find proof command. Did you mean "+completions.get(0));

                    LintProblem lp = new LintProblem(callUndefined);
                    List<Token> tokens = new ArrayList<Token>();
                    tokens.add(call.getRuleContext().getStart());
                    tokens.add(call.getRuleContext().getStop());
                    lp.setMarkTokens(tokens);
                    problems.add(lp);
                }
                return super.visit(call);
            }

        }
    }
}
