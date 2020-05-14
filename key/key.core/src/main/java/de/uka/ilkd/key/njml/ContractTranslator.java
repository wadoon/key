package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (5/12/20)
 */
@SuppressWarnings("all")
public class ContractTranslator extends JmlParserBaseVisitor<Object> {
    private SLTranslationExceptionManager excManager;
    private ImmutableSet<PositionedString> warnings = DefaultImmutableSet.<PositionedString>nil();
    private ImmutableSLList<String> mods;
    final JMLSpecFactory2 factory;
    private final KeYJavaType kjt;
    private Object currentBehavior;

    private ContractTranslator(String fileName, Position offsetPos, JMLSpecFactory2 factory, KeYJavaType kjt) throws SLTranslationException {
        this.factory = factory;
        this.kjt = kjt;
        this.excManager = new SLTranslationExceptionManager(null, fileName, offsetPos);
    }

    private PositionedString createPositionedString(String text, Token t) {
        return excManager.createPositionedString(text, new Position(t.getLine(), t.getCharPositionInLine()));
    }

    private PositionedString createPositionedString(final String text,
                                                    final Position pos) {
        return excManager.createPositionedString(text, pos);
    }


    private void raiseError(String msg) throws SLTranslationException {
        throw excManager.createException(msg);
    }


    private void raiseNotSupported(String feature) {
        PositionedString warning = excManager.createPositionedString(feature + " not supported");
        warnings = warnings.add(warning);
    }


    public ImmutableSet<PositionedString> getWarnings() {
        return warnings;
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
            raiseNotSupported("modifiers in axiom clause");
        return null;//factory.createJMLClassAxiom(kjt, mods, ctx.expression());
    }

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        for (String s : mods) {
            if (!(s.equals("public") || s.equals("private") || s.equals("protected")))
                raiseNotSupported("modifier " + s + " in initially clause");
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
}
