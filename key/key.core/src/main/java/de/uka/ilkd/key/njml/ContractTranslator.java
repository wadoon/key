package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLExceptionFactory;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (5/12/20)
 */
@SuppressWarnings("all")
public class ContractTranslator extends JmlParserBaseVisitor<Object> {
    private SLExceptionFactory exc;
    private ImmutableSet<PositionedString> warnings = DefaultImmutableSet.<PositionedString>nil();
    private ImmutableSLList<String> mods;
    final JMLSpecFactory2 factory;
    private final KeYJavaType kjt;
    private Object currentBehavior;

    private JMLSpecFactory.ContractClauses contractClauses = new JMLSpecFactory.ContractClauses();
    private List<Term> abbreviations = new ArrayList<>(64);

    public ContractTranslator(String fileName, Position offsetPos, JMLSpecFactory2 factory, KeYJavaType kjt) throws SLTranslationException {
        this.factory = factory;
        this.kjt = kjt;
        this.exc = new SLExceptionFactory(fileName, offsetPos, 0, 0);
    }

    private PositionedString flipHeaps(String declString, PositionedString result) {
        return flipHeaps(declString, result, false);
    }

    /*
     * This method prepends a String to a given PositionedString and removes whitespaces from
     * heap brackets at the beginning of it. (Why is this necessary?)
     *
     * Note: Static manipulation of Strings that are passed to KeYJMLParser is fragile when it
     * comes to error reporting. Original JML input should be left unmodified as much as possible
     * so that correct error location can be reported to the user. Functionality of this method
     * should be replaced by a more accurate implementation. (Kai Wallisch 07/2015)
     */
    private PositionedString flipHeaps(String declString, PositionedString result, boolean allowPreHeaps) {
        String t = result.text;
        String p = declString;

        List<Name> validHeapNames = new ArrayList<Name>();

        for (Name heapName : HeapLDT.VALID_HEAP_NAMES) {
            validHeapNames.add(heapName);
            if (allowPreHeaps) {
                validHeapNames.add(new Name(heapName.toString() + "AtPre"));
            }
        }
        for (Name heapName : validHeapNames) {
            t = t.trim();
            String l = "<" + heapName + ">";
            String lsp = "< " + heapName + " >";
            if (t.startsWith(l) || t.startsWith(lsp)) {
                p = l + p;
                t = t.substring(t.startsWith(lsp) ? lsp.length() : l.length());
                result = new PositionedString(t, result.fileName, result.pos);
            }
        }
        if (p.contains("<")) {
            /*
             * Using normal prepend without update of position in case p contains a heap
             * because in that case prependAndUpdatePosition() might produce a negative
             * column value. However, this alternative is also not ideal because it does
             * not update the position after prepending a string. A rewrite of this
             * method that does not rely on low-level string manipulation is recommended
             * to fix this issue.
             */
            result = result.prepend(p + " ");
        } else {
            result = result.prependAndUpdatePosition(p + " ");
        }
        return result;
    }


    private <T> @Nullable T accept(@Nullable ParserRuleContext ctx) {
        if (ctx == null) return null;
        return (T) ctx.accept(this);
    }

    private <T> List<T> mapOf(List<? extends ParserRuleContext> contexts) {
        return contexts.stream().map(it -> (T) accept(it)).collect(Collectors.toList());
    }

    private <T> ImmutableList<T> listOf(List<? extends ParserRuleContext> contexts) {
        ImmutableList<T> seq = ImmutableSLList.nil();
        for (ParserRuleContext context : contexts) {
            seq = seq.append((T) accept(context));
        }
        return seq;
    }


    @Override
    public ImmutableList<TextualJMLConstruct> visitClasslevel_comment(JmlParser.Classlevel_commentContext ctx) {
        ImmutableList<TextualJMLConstruct> result = ImmutableSLList.<TextualJMLConstruct>nil();
        this.mods = ImmutableSLList.<String>nil();
        /* there may be some modifiers after the declarations */
        this.mods = (ImmutableSLList<String>) this.<String>listOf(ctx.modifiers());
        result = listOf(ctx.classlevel_element());
        this.mods = (ImmutableSLList<String>) mods.prepend(this.mods);
        return result;
    }

    @Override
    public ImmutableList<TextualJMLConstruct> visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
        ImmutableList<TextualJMLConstruct> result = ImmutableSLList.<TextualJMLConstruct>nil();
        mods = ImmutableSLList.<String>nil();
        return null;//listOf(ctx.methodlevel_element());
    }

    @Override
    public ImmutableList<String> visitModifiers(JmlParser.ModifiersContext ctx) {
        return listOf(ctx.modifier());
    }

    @Override
    public String visitModifier(JmlParser.ModifierContext ctx) {
        return ctx.getText();
    }


    @Override
    public ClassInvariantImpl visitClass_invariant(JmlParser.Class_invariantContext ctx) {
        ImmutableList<TextualJMLConstruct> result;
        String name = null;
        ctx.expression().getText();
        Term expr = accept(ctx.expression());
        return factory.createJMLClassInvariant(kjt, mods, name, ctx.expression());
    }

    @Override
    public ClassAxiom visitClass_axiom(JmlParser.Class_axiomContext ctx) {
        // axiom statements may not be prefixed with any modifiers (see Sect. 8 of the JML reference manual)
        if (!mods.isEmpty())
            exc.raiseNotSupported("modifiers in axiom clause");
        return null;//factory.createJMLClassAxiom(kjt, mods, ctx.expression());
    }

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        for (String s : mods) {
            if (!(s.equals("public") || s.equals("private") || s.equals("protected")))
                exc.raiseNotSupported("modifier " + s + " in initially clause");
        }
        return null;// factory.createJMLInitiallyClause(kjt, mods, ctx.expression());
    }

    @Override
    public Object visitMethod_specification(JmlParser.Method_specificationContext ctx) {
        return listOf(ctx.spec_case());
    }

    private <T> @Nullable T oneOf(ParserRuleContext @Nullable ... contexts) {
        for (ParserRuleContext context : contexts) {
            T t = accept(context);
            if (t != null) return t;
        }
        return null;
    }

    @Override
    public Object visitClasslevel_element(JmlParser.Classlevel_elementContext ctx) {
        return super.visitClasslevel_element(ctx);
    }

    @Override
    public Object visitMethodlevel_element(JmlParser.Methodlevel_elementContext ctx) {
        return super.visitMethodlevel_element(ctx);
    }

    //TODO init
    IProgramMethod pm = null;

    @Override
    public Contract visitSpec_case(JmlParser.Spec_caseContext ctx) {
        this.mods = accept(ctx.modifier());
        Behavior behavior = getBehavior(ctx.behavior, pm);
        String name = factory.generateName(pm, behavior, "name");
        contractClauses.clear();
        accept(ctx.spec_body());
        //factory.createFunctionalOperationContracts();
        return null;
    }

    private Behavior getBehavior(Token behavior, IProgramMethod pm) {
        //TODO missing model behavior
        if (behavior == null) return Behavior.BEHAVIOR;
        return Behavior.valueOf(behavior.getText());
    }

    @Override
    public Object visitSpec_body(JmlParser.Spec_bodyContext ctx) {
        listOf(ctx.clause());
        listOf(ctx.spec_body());
        return super.visitSpec_body(ctx);
    }

    @Override
    public Object visitSimple_clause(JmlParser.Simple_clauseContext ctx) {
        String type = ctx.simple_clause_keyword().getText();
        Term t = factory.parseExpress(ctx.predornot());
        String clause = ctx.simple_clause_keyword().getText();
        Term term = accept(ctx.predornot());
        contractClauses.put(clause, term);

        translator.translate(ens.getText(), Term.class, result, services);
    }

    @Override
    public Object visitSimple_clause_keyword(JmlParser.Simple_clause_keywordContext ctx) {
        return super.visitSimple_clause_keyword(ctx);
    }

    @Override
    public Object visitAccessible_clause(JmlParser.Accessible_clauseContext ctx) {
        return super.visitAccessible_clause(ctx);
    }

    @Override
    public Object visitAssignable_clause(JmlParser.Assignable_clauseContext ctx) {
        return super.visitAssignable_clause(ctx);
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
        @init {
            Term pred = null;
            String vName = null;
            LogicVariable eVar = null;
        }
        @after{ret=result;}
:
        sig=SIGNALS LPAREN excType=referencetype (id=IDENT { vName = id.getText(); })? RPAREN
        {
            if (vName != null) {
                eVar = new LogicVariable(new Name(vName), excType.getSort());
                resolverManager.pushLocalVariablesNamespace();
                resolverManager.putIntoTopLocalVariablesNamespace(eVar, excType);
            }
        }
        (result = predornot)?
                {
        if (vName != null) {
            resolverManager.popLocalVariablesNamespace();
        }
        result = translator.translate(sig.getText(), Term.class, result, eVar, excVar, excType, services);
    }
        ;

    }

    @Override
    public Object visitSignals_only_clause(JmlParser.Signals_only_clauseContext ctx) {
        List<Object> types = mapOf(ctx.referencetype());
        translator.translate(sigo.getText(), Term.class, typeList, this.excVar, services);
        return null;
    }

    @Override
    public Object visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        Label id = accept(ctx.IDENT());
        Term pred = accept(ctx.predornot());
        translator.translate(breaks.getText(), Pair.class, pred, label, services);
    }

    @Override
    public Object visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        continues=CONTINUES LPAREN (id=IDENT { label = id.getText(); })? RPAREN
                (pred = predornot)?
                        result = translator.translate(continues.getText(), Pair.class, pred, label, services);
    }

    @Override
    public Object visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        return factory.get(rtrns.getText(), Term.class, result, services);

    }

    @Override
    public Object visitName_clause(JmlParser.Name_clauseContext ctx) {
        return super.visitName_clause(ctx);
    }

    @Override
    public Object visitOld_clause(JmlParser.Old_clauseContext ctx) {
        return super.visitOld_clause(ctx);
    }

    @Override
    public Object visitField_or_method_declaration(JmlParser.Field_or_method_declarationContext ctx) {
        return super.visitField_or_method_declaration(ctx);
    }

    @Override
    public Object visitField_declaration(JmlParser.Field_declarationContext ctx) {
        return super.visitField_declaration(ctx);
    }

    @Override
    public Object visitMethod_declaration(JmlParser.Method_declarationContext ctx) {
        return super.visitMethod_declaration(ctx);
    }

    @Override
    public Object visitParam_list(JmlParser.Param_listContext ctx) {
        return super.visitParam_list(ctx);
    }

    @Override
    public Object visitParam_decl(JmlParser.Param_declContext ctx) {
        return super.visitParam_decl(ctx);
    }

    @Override
    public Object visitHistory_constraint(JmlParser.History_constraintContext ctx) {
        return super.visitHistory_constraint(ctx);
    }

    @Override
    public Object visitDatagroup_clause(JmlParser.Datagroup_clauseContext ctx) {
        return super.visitDatagroup_clause(ctx);
    }

    @Override
    public Object visitMonitors_for_clause(JmlParser.Monitors_for_clauseContext ctx) {
        return super.visitMonitors_for_clause(ctx);
    }

    @Override
    public Object visitReadable_if_clause(JmlParser.Readable_if_clauseContext ctx) {
        return super.visitReadable_if_clause(ctx);
    }

    @Override
    public Object visitWritable_if_clause(JmlParser.Writable_if_clauseContext ctx) {
        return super.visitWritable_if_clause(ctx);
    }

    @Override
    public Object visitIn_group_clause(JmlParser.In_group_clauseContext ctx) {
        return super.visitIn_group_clause(ctx);
    }

    @Override
    public Object visitMaps_into_clause(JmlParser.Maps_into_clauseContext ctx) {
        return super.visitMaps_into_clause(ctx);
    }

    @Override
    public Object visitNowarn_pragma(JmlParser.Nowarn_pragmaContext ctx) {
        return super.visitNowarn_pragma(ctx);
    }


    @Override
    public Object visitDebug_statement(JmlParser.Debug_statementContext ctx) {
        return super.visitDebug_statement(ctx);
    }

    @Override
    public Object visitSet_statement(JmlParser.Set_statementContext ctx) {
        return super.visitSet_statement(ctx);
    }

    @Override
    public Object visitMerge_point_statement(JmlParser.Merge_point_statementContext ctx) {
        return super.visitMerge_point_statement(ctx);
    }

    @Override
    public Object visitLoop_specification(JmlParser.Loop_specificationContext ctx) {
        return super.visitLoop_specification(ctx);
    }

    @Override
    public Object visitLoop_invariant(JmlParser.Loop_invariantContext ctx) {
        return super.visitLoop_invariant(ctx);
    }

    @Override
    public Object visitVariant_function(JmlParser.Variant_functionContext ctx) {
        return super.visitVariant_function(ctx);
    }

    @Override
    public Object visitInitialiser(JmlParser.InitialiserContext ctx) {
        return super.visitInitialiser(ctx);
    }

    @Override
    public Object visitBlock_specification(JmlParser.Block_specificationContext ctx) {
        return super.visitBlock_specification(ctx);
    }

    @Override
    public Object visitBlock_loop_specification(JmlParser.Block_loop_specificationContext ctx) {
        return super.visitBlock_loop_specification(ctx);
    }

    @Override
    public Object visitLoop_contract_keyword(JmlParser.Loop_contract_keywordContext ctx) {
        return super.visitLoop_contract_keyword(ctx);
    }

    @Override
    public Object visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        return super.visitAssert_statement(ctx);
    }

    @Override
    public Object visitAssume_statement(JmlParser.Assume_statementContext ctx) {
        return super.visitAssume_statement(ctx);
    }

}
