package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.njml.JmlFacade.TODO;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec.ClauseHd.INVARIANT_FREE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.*;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;

class TextualTranslator extends JmlParserBaseVisitor<Object> {
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
    public Object visitClasslevel_element0(JmlParser.Classlevel_element0Context ctx) {
        mods = ImmutableSLList.nil();
        accept(ctx.modifiers());
        accept(ctx.classlevel_element());
        acceptAll(ctx.modifier2());
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
        loopContract = null;
        constructs = constructs.append(methodContract);
        super.visitSpec_case(ctx);
        methodContract = null;
        return null;
    }

    private Behavior getBehavior(Token behavior) {
        if (behavior == null) {
            return Behavior.NONE; // lightweight specification
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
        throw new IllegalStateException("No behavior is given");
    }

    @Override
    public Object visitSpec_body(JmlParser.Spec_bodyContext ctx) {
        acceptAll(ctx.a);
        if (ctx.NEST_START() != null) {
            final TextualJMLSpecCase base = methodContract;
            if (ctx.inner != null) {
                assert base != null;
                methodContract = base.clone();
                constructs = constructs.append(methodContract);
                acceptAll(ctx.inner);
            }

            for (JmlParser.Spec_bodyContext it : ctx.spec_body()) {
                assert base != null;
                methodContract = base.clone();
                constructs = constructs.append(methodContract);
                accept(it);
            }
        }
        return null;
    }

    @Override
    public Name[] visitTargetHeap(JmlParser.TargetHeapContext ctx) {
        if (ctx == null || ctx.SPECIAL_IDENT().size() == 0) {
            return new Name[]{HeapLDT.BASE_HEAP_NAME};
        }
        Name[] heaps = new Name[ctx.SPECIAL_IDENT().size()];
        for (int i = 0; i < ctx.SPECIAL_IDENT().size(); i++) {
            String t = ctx.SPECIAL_IDENT(i).getText();
            heaps[i] = new Name(t.substring(1, t.length() - 1));
        }
        return heaps;
    }

    @Override
    public Object visitEnsures_clause(JmlParser.Ensures_clauseContext ctx) {
        assert methodContract != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            methodContract.addClause(
                    ctx.ENSURES().getText().endsWith("_free")
                            ? ENSURES_FREE
                            : ENSURES,
                    heap,
                    ctx);
        }
        return null;
    }

    @Override
    public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        assert methodContract != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            methodContract.addClause(
                    ctx.REQUIRES().getText().endsWith("_free")
                            ? REQUIRES_FREE
                            : REQUIRES,
                    heap, ctx);
        }
        return null;
    }

    @Override
    public Object visitMeasured_by_clause(JmlParser.Measured_by_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(MEASURED_BY, ctx);
        return null;
    }

    @Override
    public Object visitCaptures_clause(JmlParser.Captures_clauseContext ctx) {
        //methodContract.addClause(CAPTURES, ctx)
        TODO();
        return null;
    }

    @Override
    public Object visitDiverges_clause(JmlParser.Diverges_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(DIVERGES, ctx);
        return null;
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
        assert methodContract != null;
        boolean depends = ctx.MEASURED_BY() != null || ctx.COLON() != null;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            if (depends) {
                TextualJMLDepends d = new TextualJMLDepends(mods, new LabeledParserRuleContext(ctx));
                constructs = constructs.append(d);
            } else if (methodContract != null) {
                methodContract.addClause(ACCESSIBLE, heap, ctx);
            } else {
                assert false;
            }
        }
        return null;
    }

    @Override
    public Object visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            if (methodContract != null) {
                methodContract.addClause(ASSIGNABLE, heap, ctx);
            }
            if (loopContract != null) {
                loopContract.addClause(TextualJMLLoopSpec.ClauseHd.ASSIGNABLE, heap, new LabeledParserRuleContext(ctx));
            }
        }
        return null;
    }

    @Override
    public Object visitVariant_function(JmlParser.Variant_functionContext ctx) {
        if (loopContract != null)
            loopContract.setVariant(new LabeledParserRuleContext(ctx, null));
        else
            methodContract.addClause(DECREASES, ctx);
        return null;
    }

    /*    @Override
    public Object visitDepends_clause(JmlParser.Depends_clauseContext ctx) {
        TextualJMLDepends depends = new TextualJMLDepends(mods, ctx);
        constructs = constructs.append(depends);
        return null;
    }*/

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        TextualJMLInitially initially = new TextualJMLInitially(mods, new LabeledParserRuleContext(ctx, null));
        constructs = constructs.append(initially);
        return null;
    }

    @Override
    public Object visitRepresents_clause(JmlParser.Represents_clauseContext ctx) {
        TextualJMLRepresents represents = new TextualJMLRepresents(mods, new LabeledParserRuleContext(ctx));
        constructs = constructs.append(represents);
        return super.visitRepresents_clause(ctx);
    }

    @Override
    public Object visitSeparates_clause(JmlParser.Separates_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(INFORMATION_FLOW, ctx);
        return null;
    }

    @Override
    public Object visitLoop_separates_clause(JmlParser.Loop_separates_clauseContext ctx) {
        assert loopContract != null;
        loopContract.addClause(TextualJMLLoopSpec.Clause.INFORMATION_FLOW, new LabeledParserRuleContext(ctx));
        return null;
    }

    @Override
    public Object visitDetermines_clause(JmlParser.Determines_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(INFORMATION_FLOW, ctx);
        return null;
    }

    @Override
    public Object visitLoop_determines_clause(JmlParser.Loop_determines_clauseContext ctx) {
        TODO();
        //loopContract.addClause(TextualJMLLoopSpec.Clause.INFORMATION_FLOW, ctx);
        return super.visitLoop_determines_clause(ctx);
    }

    @Override
    public Object visitSignals_clause(JmlParser.Signals_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(SIGNALS, ctx);
        return this;
    }

    @Override
    public Object visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(SIGNALS_ONLY, ctx);
        return null;
    }

    @Override
    public Object visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(BREAKS, ctx);
        return null;
    }

    @Override
    public Object visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(CONTINUES, ctx);
        return null;
    }

    @Override
    public Object visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        assert methodContract != null;
        methodContract.addClause(RETURNS, ctx);
        return null;
    }

    @Override
    public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
        TODO();
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
        TextualJMLClassAxiom inv = new TextualJMLClassAxiom(mods, new LabeledParserRuleContext(ctx, null));
        constructs = constructs.append(inv);
        return null;
    }


    @Override
    public Object visitField_declaration(JmlParser.Field_declarationContext ctx) {
        assert mods.size() > 0;
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
        methodContract = null;
        constructs = constructs.append(loopContract);
        super.visitLoop_specification(ctx);
        loopContract = null;
        return null;
    }

    @Override
    public Object visitMerge_point_statement(JmlParser.Merge_point_statementContext ctx) {
        TextualJMLMergePointDecl mergePointDecl = new TextualJMLMergePointDecl(mods, ctx);
        constructs = constructs.append(mergePointDecl);
        return null;
    }

    @Override
    public Object visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
        assert loopContract != null;
        TextualJMLLoopSpec.ClauseHd type = ctx.LOOP_INVARIANT().getText().endsWith("_free") ? INVARIANT_FREE : INVARIANT;
        Name[] heaps = visitTargetHeap(ctx.targetHeap());
        for (Name heap : heaps) {
            loopContract.addClause(type, heap, new LabeledParserRuleContext(ctx));
        }
        return null;
    }


    @Override
    public Object visitAssume_statement(JmlParser.Assume_statementContext ctx) {
        TextualJMLSpecCase b = new TextualJMLSpecCase(ImmutableSLList.nil(), Behavior.NONE);
        constructs = constructs.prepend(b);
        b.addClause(ENSURES_FREE, ctx);
        return null;
    }


    @Override
    public Object visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        /*
             * Produce a (textual) block contract from a JML assert statement.
             * The resulting contract has an empty precondition, the assert expression
             * as a postcondition, and strictly_nothing as frame.
            public static TextualJMLSpecCase assert2blockContract(ImmutableList<String> mods, PositionedString assertStm) {
                final TextualJMLSpecCase res = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
                res.addName(new PositionedString("assert " + assertStm.text, assertStm.fileName, assertStm.pos));
                res.addClause(Clause.ENSURES, assertStm);
                res.addClause(Clause.ASSIGNABLE, new PositionedString("assignable \\strictly_nothing;", assertStm.fileName, assertStm.pos));
                res.setPosition(assertStm);
                return res;
            }
            */
        TextualJMLSpecCase b = new TextualJMLSpecCase(ImmutableSLList.nil(), Behavior.NORMAL_BEHAVIOR);
        constructs = constructs.prepend(b);
        b.addName("assert " + ctx.getText());
        b.addClause(ENSURES, ctx);
        b.addClause(ASSIGNABLE, JmlFacade.parseClause("assignable \\strictly_nothing;"));
        return null;
    }

    @Override
    public Object visitBlock_specification(JmlParser.Block_specificationContext ctx) {
        accept(ctx.method_specification());
        return null;
    }

    @Override
    public Object visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
        acceptAll(ctx.spec_case());
        for (TextualJMLConstruct construct : constructs) {
            construct.setLoopContract(true);
        }
        return null;
    }
}
