package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import org.antlr.v4.runtime.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT_FREE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS_ONLY;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;

/**
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
public class JmlFacade {
    public static JmlLexer createLexer(CharStream strea) {
        JmlLexer lexer = new JmlLexer(strea);
        return lexer;
    }

    public static JmlLexer createLexer(PositionedString ps) {
        CharStream result = CharStreams.fromString(ps.text, ps.fileName);
        JmlLexer lexer = createLexer(result);
        lexer._tokenStartCharPositionInLine = ps.pos.getColumn();
        lexer._tokenStartLine = 1 + ps.pos.getLine();
        return lexer;
    }

    public static JmlLexer createLexer(String expr) {
        return createLexer(CharStreams.fromString(expr));
    }

    public static JmlParser.ExpressionContext parseExpr(PositionedString expr) {
        final JmlLexer lexer = createLexer(expr);
        lexer._mode = JmlLexer.expr;
        JmlParser parser = createParser(lexer);
        return parser.expressionEOF().expression();
    }

    public static JmlParser.ExpressionContext parseExpr(String expr) {
        final JmlLexer lexer = createLexer(expr);
        lexer._mode = JmlLexer.expr;
        JmlParser parser = createParser(lexer);
        return parser.expressionEOF().expression();
    }

    static JmlParser createParser(JmlLexer lexer) {
        JmlParser p = new JmlParser(new CommonTokenStream(lexer));
        p.addErrorListener(new BaseErrorListener() {
            @Override
            public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e) {
                Token t = (Token) offendingSymbol;
                throw new RuntimeException("line " + line + ":" + charPositionInLine + " " + msg);
            }
        });
        return p;
    }

    public static ParserRuleContext parseTop(PositionedString expr) {
        JmlParser p = createParser(createLexer(expr));
        return p.classlevel_comments();
    }

    public static ParserRuleContext parseClause(String s) {
        JmlParser p = createParser(createLexer(s));
        return p.clause();//TODO EOF
    }

    static ImmutableList<TextualJMLConstruct> parseClasslevel(JmlLexer lexer) {
        @NotNull JmlParser p = createParser(lexer);
        JmlParser.Classlevel_commentsContext ctx = p.classlevel_comments();
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        return translator.constructs;
    }

    public static ImmutableList<TextualJMLConstruct> parseClasslevel(PositionedString positionedString) {
        return parseClasslevel(createLexer(positionedString));
    }

    public static ImmutableList<TextualJMLConstruct> parseClasslevel(String string) {
        return parseClasslevel(createLexer(string));
    }

    public static ImmutableList<TextualJMLConstruct> parseMethodlevel(PositionedString positionedString) {
        return parseMethodlevel(createLexer(positionedString));
    }

    private static ImmutableList<TextualJMLConstruct> parseMethodlevel(JmlLexer lexer) {
        @NotNull JmlParser p = createParser(lexer);
        JmlParser.Methodlevel_commentContext ctx = p.methodlevel_comment();
        TextualTranslator translator = new TextualTranslator();
        ctx.accept(translator);
        return translator.constructs;
    }

    static class TextualTranslator extends JmlParserBaseVisitor<Object> {
        public ImmutableList<TextualJMLConstruct> constructs = ImmutableSLList.nil();
        private ImmutableList<String> mods = ImmutableSLList.nil();
        @Nullable
        private TextualJMLSpecCase methodContract;
        @Nullable
        private TextualJMLLoopSpec loopContract;

        @Override
        public Object visitModifier(JmlParser.ModifierContext ctx) {
            mods = mods.append(ctx.getText());
            return null;
        }

        @Override
        public Object visitClasslevel_comment(JmlParser.Classlevel_commentContext ctx) {
            mods = ImmutableSLList.nil();
            acceptAll(ctx.modifiers());
            for (JmlParser.Classlevel_elementContext c : ctx.classlevel_element()) {
                c.accept(this);
            }
            return null;
        }

        @Override
        public Object visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
            return super.visitMethodlevel_comment(ctx);
        }


        @Override
        public Object visitSpec_case(JmlParser.Spec_caseContext ctx) {
            Behavior behaviour = getBehavior(ctx.behavior);
            methodContract = new TextualJMLSpecCase(mods, behaviour);
            constructs = constructs.append(methodContract);
            return super.visitSpec_case(ctx);
        }

        private Behavior getBehavior(Token behavior) {
            if (behavior == null) {
                return Behavior.BEHAVIOR;
            }

            switch (behavior.getType()) {
                case JmlLexer.BEHAVIOR:
                    return Behavior.BEHAVIOR;
                case JmlLexer.NORMAL_BEHAVIOR:
                    return Behavior.NORMAL_BEHAVIOR;
                case JmlLexer.BREAK_BEHAVIOR:
                    return Behavior.BREAK_BEHAVIOR;
                case JmlLexer.EXCEPTIONAL_BEHAVIOUR:
                    return Behavior.EXCEPTIONAL_BEHAVIOR;
                case JmlLexer.MODEL_BEHAVIOUR:
                    return Behavior.MODEL_BEHAVIOR;
                case JmlLexer.RETURN_BEHAVIOR:
                    return Behavior.RETURN_BEHAVIOR;
                case JmlLexer.CONTINUE_BEHAVIOR:
                    return Behavior.CONTINUE_BEHAVIOR;
            }
            return null;
        }

        @Override
        public Object visitSpec_body(JmlParser.Spec_bodyContext ctx) {
            acceptAll(ctx.a);
            if (ctx.NEST_START() != null) {
                final TextualJMLSpecCase base = methodContract;
                if (ctx.inner != null) {
                    methodContract = base.clone();
                    constructs = constructs.append(methodContract);
                    acceptAll(ctx.inner);
                }

                for (JmlParser.Spec_bodyContext it : ctx.spec_body()) {
                    methodContract = base.clone();
                    constructs = constructs.append(methodContract);
                    accept(it);
                }
            }
            return null;
        }

        @Override
        public Object visitTargetHeap(JmlParser.TargetHeapContext ctx) {
            return new Name(ctx.ident().getText());
        }

        @Override
        public Object visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
            methodContract.addClause(
                    ctx.ENSURES().getText().endsWith("_free")
                            ? ENSURES_FREE
                            : ENSURES,
                    accept(ctx.targetHeap()),
                    ctx);
            return null;
        }

        @Override
        public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
            methodContract.addClause(
                    ctx.REQUIRES().getText().endsWith("_free")
                            ? REQUIRES_FREE
                            : REQUIRES,
                    ctx);
            return null;
        }


        @Override
        public Object visitMeasured_by_clause(JmlParser.Measured_by_clauseContext ctx) {
            return super.visitMeasured_by_clause(ctx);
        }

        @Override
        public Object visitCaputures_clause(JmlParser.Caputures_clauseContext ctx) {
            return super.visitCaputures_clause(ctx);
        }

        @Override
        public Object visitDiverges_clause(JmlParser.Diverges_clauseContext ctx) {
            return super.visitDiverges_clause(ctx);
        }

        @Override
        public Object visitWorking_space_clause(JmlParser.Working_space_clauseContext ctx) {
            return super.visitWorking_space_clause(ctx);
        }

        @Override
        public Object visitDuration_clause(JmlParser.Duration_clauseContext ctx) {
            return super.visitDuration_clause(ctx);
        }

        @Override
        public Object visitWhen_clause(JmlParser.When_clauseContext ctx) {
            return super.visitWhen_clause(ctx);
        }

        @Override
        public Object visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
            methodContract.addClause(ACCESSIBLE, accept(ctx.targetHeap()), ctx);
            return null;
        }

        @Override
        public Object visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
            methodContract.addClause(ASSIGNABLE, accept(ctx.targetHeap()), ctx);
            return null;
        }

        @Override
        public Object visitDepends_clause(JmlParser.Depends_clauseContext ctx) {
            return super.visitDepends_clause(ctx);
        }

        @Override
        public Object visitRepresents_clause(JmlParser.Represents_clauseContext ctx) {
            return super.visitRepresents_clause(ctx);
        }

        @Override
        public Object visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
            return super.visitSeparates_clause(ctx);
        }

        @Override
        public Object visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
            return super.visitLoop_separates_clause(ctx);
        }

        @Override
        public Object visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
            return super.visitDetermines_clause(ctx);
        }

        @Override
        public Object visitLoop_determines_clause(JmlParser.Loop_determines_clauseContext ctx) {
            return super.visitLoop_determines_clause(ctx);
        }

        @Override
        public Object visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
            methodContract.addClause(SIGNALS, ctx);
            return this;

        }

        @Override
        public Object visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
            methodContract.addClause(SIGNALS_ONLY, ctx);
            return this;
        }

        @Override
        public Object visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
            return super.visitBreaks_clause(ctx);
        }

        @Override
        public Object visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
            return super.visitContinues_clause(ctx);
        }

        @Override
        public Object visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
            return super.visitReturns_clause(ctx);
        }

        @Override
        public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
            return super.visitName_clause(ctx);
        }

        private void acceptAll(Iterable<? extends ParserRuleContext> ctxs) {
            for (ParserRuleContext ctx : ctxs) {
                accept(ctx);
            }
        }

        private <T> T accept(ParserRuleContext ctx) {
            if (ctx == null) return null;
            return (T) ctx.accept(this);
        }

        @Override
        public Object visitMethodlevel_element(JmlParser.Methodlevel_elementContext ctx) {
            return super.visitMethodlevel_element(ctx);
        }

        @Override
        public Object visitModifiers(JmlParser.ModifiersContext ctx) {
            for (JmlParser.ModifierContext modifierContext : ctx.modifier()) {

            }
            return super.visitModifiers(ctx);
        }

        @Override
        public Object visitClass_invariant(JmlParser.Class_invariantContext ctx) {
            TextualJMLClassInv inv = new TextualJMLClassInv(mods, ctx);
            constructs = constructs.append(inv);
            return null;
        }

        @Override
        public Object visitClass_axiom(JmlParser.Class_axiomContext ctx) {
            TextualJMLClassAxiom inv = new TextualJMLClassAxiom(mods, ctx);
            constructs = constructs.append(inv);
            return null;
        }


        @Override
        public Object visitField_declaration(JmlParser.Field_declarationContext ctx) {
            TextualJMLFieldDecl inv = new TextualJMLFieldDecl(mods, ctx);
            constructs = constructs.append(inv);
            return null;
        }

        @Override
        public Object visitMethod_declaration(JmlParser.Method_declarationContext ctx) {
            TextualJMLMethodDecl inv = new TextualJMLMethodDecl(mods, ctx);
            constructs = constructs.append(inv);
            return null;
        }

        @Override
        public Object visitSet_statement(JmlParser.Set_statementContext ctx) {
            TextualJMLSetStatement inv = new TextualJMLSetStatement(mods, ctx);
            constructs = constructs.append(inv);
            return null;
        }

        @Override
        public Object visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
            loopContract = new TextualJMLLoopSpec(mods);
            constructs = constructs.append(methodContract);
            return null;
        }

        @Override
        public Object visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
            assert loopContract != null;
            TextualJMLLoopSpec.ClauseHd type = ctx.LOOP_INVARIANT().getText().endsWith("_free") ? INVARIANT_FREE : INVARIANT;
            loopContract.addClause(type, ctx);
            return null;
        }

        @Override
        public Object visitAssume_statement(JmlParser.Assume_statementContext ctx) {
            return null;
        }

        @Override
        public Object visitBlock_specification(JmlParser.Block_specificationContext ctx) {
            return super.visitBlock_specification(ctx);
        }

        @Override
        public Object visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
            return super.visitBlock_loop_specification(ctx);
        }
    }
}
