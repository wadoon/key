package org.key_project.key.tptp;

import de.uka.ilkd.key.tptp.tptp_v7_0_0_0BaseVisitor;
import de.uka.ilkd.key.tptp.tptp_v7_0_0_0Lexer;
import de.uka.ilkd.key.tptp.tptp_v7_0_0_0Parser;
import org.antlr.v4.runtime.ParserRuleContext;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

import static org.key_project.key.tptp.TargetFile.DEFAULT_SORT;


public class Tptp2KeyTranslator extends tptp_v7_0_0_0BaseVisitor<Object> {
    private final Path currentPath;
    TargetFile output;

    Tptp2KeyTranslator(Path currentPath, TargetFile output) {
        this.currentPath = currentPath;
        this.output = output;
    }

    public Tptp2KeyTranslator(Path currentPath) {
        this(currentPath, new TargetFile());
    }

    @Override
    public Object visitInclude(tptp_v7_0_0_0Parser.IncludeContext ctx) {
        var path = ctx.file_name().getText();
        var newPath = currentPath.getParent().resolve(path);
        try {
            Facade.include(newPath, this);
        } catch (IOException e) {
            throw new RuntimeException("Could not include file: " + newPath, e);
        }
        return null;
    }

    @Override
    public Object visitTpi_annotated(tptp_v7_0_0_0Parser.Tpi_annotatedContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitTpi_formula(tptp_v7_0_0_0Parser.Tpi_formulaContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitThf_annotated(tptp_v7_0_0_0Parser.Thf_annotatedContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitTfx_annotated(tptp_v7_0_0_0Parser.Tfx_annotatedContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitTff_annotated(tptp_v7_0_0_0Parser.Tff_annotatedContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitTcf_annotated(tptp_v7_0_0_0Parser.Tcf_annotatedContext ctx) {
        throw new IllegalStateException();
    }

    @Override
    public Object visitFof_annotated(tptp_v7_0_0_0Parser.Fof_annotatedContext ctx) {
        // ignore name in KeY: ctx.name()
        var role = ctx.formula_role().getText();
        var formula = ctx.fof_formula().accept(new FofFormulaTranslator());

        output.sorts.ensure(DEFAULT_SORT);

        //<formula_role>         :== axiom | hypothesis | definition | assumption |
        //                           lemma | theorem | corollary | conjecture |
        //                           negated_conjecture | plain | type |
        //                           fi_domain | fi_functors | fi_predicates | unknown
        switch (role) {
            case "axiom", "definition", "assumption", "lemma", "theorem", "corollary" -> output.axioms.append(formula);
            case "conjecture", "negated_conjecture" -> output.prop.append(formula);
            default -> throw new IllegalStateException();
        }
        return null;
    }

    @Override
    public Object visitCnf_annotated(tptp_v7_0_0_0Parser.Cnf_annotatedContext ctx) {
        throw new IllegalStateException();
    }


    public class FofFormulaTranslator extends VisitorHelper<String> {
        boolean predicateMode = true;

        @Override
        public String visitFof_binary_nonassoc(tptp_v7_0_0_0Parser.Fof_binary_nonassocContext ctx) {
            var left = visitFof_unitary_formula(ctx.fof_unitary_formula(0));
            var right = visitFof_unitary_formula(ctx.fof_unitary_formula(1));
            return switch (ctx.binary_connective().start.getType()) {
                case tptp_v7_0_0_0Lexer.If -> "(%s %s %s)".formatted(left, "->", right);
                case tptp_v7_0_0_0Lexer.Impl -> "(%s %s %s)".formatted(left, "->", right);
                case tptp_v7_0_0_0Lexer.Iff -> "(%s %s %s)".formatted(left, "<->", right);
                case tptp_v7_0_0_0Lexer.Niff -> "!(%s %s %s)".formatted(left, "<->", right);
                case tptp_v7_0_0_0Lexer.Nor -> "!(%s %s %s)".formatted(left, "|", right);
                case tptp_v7_0_0_0Lexer.Nand -> "!(%s %s %s)".formatted(left, "&", right);
                default -> throw new IllegalStateException("Unexpected value: " + ctx.getText());
            };
        }

        @Override
        public String visitFof_or_formula(tptp_v7_0_0_0Parser.Fof_or_formulaContext ctx) {
            var left = visitFof_unitary_formula(ctx.fof_unitary_formula());
            if (ctx.fof_or_formula() == null) return left;
            var right = visitFof_or_formula(ctx.fof_or_formula());
            return "(%s %s %s)".formatted(left, "|", right);
        }

        @Override
        public String visitFof_and_formula(tptp_v7_0_0_0Parser.Fof_and_formulaContext ctx) {
            var left = visitFof_unitary_formula(ctx.fof_unitary_formula());
            if (ctx.fof_and_formula() == null) return left;
            var right = visitFof_and_formula(ctx.fof_and_formula());
            return "(%s %s %s)".formatted(left, "&", right);
        }

        @Override
        public String visitFof_quantified_formula(tptp_v7_0_0_0Parser.Fof_quantified_formulaContext ctx) {
            var quantifier = visitFof_quantifier(ctx.fof_quantifier());
            var formula = visitFof_unitary_formula(ctx.fof_unitary_formula());

            return "(" + ctx.fof_variable_list().variable().stream()
                    .map(it -> quantifier + " " + DEFAULT_SORT + " " + it.getText() + "; ")
                    .collect(Collectors.joining(" "))
                    + formula + ")";
        }


        @Override
        public String visitFof_unary_formula(tptp_v7_0_0_0Parser.Fof_unary_formulaContext ctx) {
            return super.visitFof_unary_formula(ctx);
        }

        @Override
        public String visitFof_infix_unary(tptp_v7_0_0_0Parser.Fof_infix_unaryContext ctx) {
            var left = visitFof_term(ctx.fof_term(0));
            var right = visitFof_term(ctx.fof_term(1));
            return "(%s %s %s)".formatted(left, "!=", right);
        }

        @Override
        public String visitFof_plain_term(tptp_v7_0_0_0Parser.Fof_plain_termContext ctx) {
            if (ctx.constant() != null) return ctx.constant().accept(this);
            var f = ctx.functor().getText();
            var args = ctx.fof_arguments().fof_term()
                    .stream().map(it -> accept(it, false))
                    .collect(Collectors.joining(", "));
            if (predicateMode)
                definePredicate(f, ctx.fof_arguments().fof_term()
                        .stream().map(it -> DEFAULT_SORT).collect(Collectors.toList()));
            else
                defineFunction(f, DEFAULT_SORT, ctx.fof_arguments().fof_term()
                        .stream().map(it -> DEFAULT_SORT).collect(Collectors.toList()));

            return "%s(%s)".formatted(f, args);
        }

        private String accept(ParserRuleContext ctx, boolean pm) {
            var old = this.predicateMode;
            predicateMode = pm;
            try {
                return accept(ctx);
            } finally {
                predicateMode = old;
            }
        }

        @Override
        public String visitFunctor(tptp_v7_0_0_0Parser.FunctorContext ctx) {
            return ctx.getText();
        }

        @Override
        public String visitNumber(tptp_v7_0_0_0Parser.NumberContext ctx) {
            return ctx.getText();
        }

        @Override
        public String visitVariable(tptp_v7_0_0_0Parser.VariableContext ctx) {
            return ctx.getText();
        }

        @Override
        public String visitFof_quantifier(tptp_v7_0_0_0Parser.Fof_quantifierContext ctx) {
            if (ctx.Forall() != null) return "\\forall";
            else return "\\exists";
        }
    }

    private void definePredicate(String f, List<String> sorts) {
        output.predicates.ensure(
                "%s(%s)".formatted(f, String.join(", ", sorts))
        );
    }

    private void defineFunction(String f, String retSort, List<String> sorts) {
        output.functions.ensure(
                "%s %s(%s)".formatted(retSort, f, String.join(", ", sorts))
        );
    }
}
