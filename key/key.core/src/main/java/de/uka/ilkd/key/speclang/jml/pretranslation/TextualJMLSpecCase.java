// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.njml.JmlParser;
import de.uka.ilkd.key.speclang.PositionedLabeledString;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.Triple;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;

import java.util.*;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.*;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;

/**
 * A JML specification case (i.e., more or less an operation contract) in
 * textual form. Is also used for block contracts.
 */
public final class TextualJMLSpecCase extends TextualJMLConstruct {
    public ImmutableList<ParserRuleContext> getRequiresFree(String toString) {
        return getList(REQUIRES_FREE, toString);
    }

    public ImmutableList<ParserRuleContext> getEnsuresFree(String toString) {
        return getList(ENSURES_FREE, toString);
    }

    private ImmutableList<ParserRuleContext> getList(ClauseHd clause, String heap) {
        return getList(clause, heap);
    }

    public ImmutableList<ParserRuleContext> getAccessible(String toString) {
        return getList(ACCESSIBLE, toString);
    }

    public ImmutableList<ParserRuleContext> getAxioms(String toString) {
        return getList(AXIOMS, toString);
    }

    public ImmutableList<ParserRuleContext> getEnsures(String toString) {
        return getList(ENSURES, toString);
    }

    public ImmutableList<ParserRuleContext> getRequires(String toString) {
        return getList(REQUIRES, toString);
    }

    public ImmutableList<ParserRuleContext> getAssignable(String toString) {
        return getList(ASSIGNABLE, toString);
    }

    public ImmutableList<ParserRuleContext> getDecreases() {
        return getList(DECREASES);
    }

    public void addAssignable(String toString, JmlParser.ExpressionContext parseExpr) {
    }

    /**
     * Heap-independent clauses
     */
    public enum Clause {
        MEASURED_BY,
        WORKING_SPACE,
        SIGNALS,
        DIVERGES,
        DEPENDS,
        BREAKS,
        CONTINUES,
        RETURNS,
        DECREASES,
        SIGNALS_ONLY,
        ABBREVIATION,
        INFORMATION_FLOW
    }

    /**
     * Heap-dependent clauses
     */
    public enum ClauseHd {
        ACCESSIBLE,
        ASSIGNABLE,
        REQUIRES,
        REQUIRES_FREE,
        ENSURES,
        ENSURES_FREE,
        AXIOMS,
        INVARIANT,
        INVARIANT_FREE
    }
    //private ImmutableList<Triple<PositionedString, PositionedString, PositionedString>> abbreviations = ImmutableSLList.nil();

    private final Behavior behavior;
    private Map<Object, List<ParserRuleContext>> clauses = new HashMap<>();
    private Map<ParserRuleContext, Name> heaps = new HashMap<>();

    public TextualJMLSpecCase(ImmutableList<String> mods, Behavior behavior) {
        super(mods);
        assert behavior != null;
        this.behavior = behavior;
        for (Name hName : HeapLDT.VALID_HEAP_NAMES) {
            //heaps.put(hName.toString(), new ArrayList<>(32));
            //accessibles.put(hName.toString() + "AtPre", ImmutableSLList.nil());
        }
    }

    public TextualJMLSpecCase addClause(Clause clause, ParserRuleContext ctx) {
        clauses.computeIfAbsent(clause, it -> new ArrayList<>()).add(ctx);
        return this;
    }

    public TextualJMLSpecCase addClause(ClauseHd clause, ParserRuleContext ctx) {
        return addClause(clause, null, ctx);
    }

    public TextualJMLSpecCase addClause(ClauseHd clause, @Nullable Name heapName, ParserRuleContext ctx) {
        if (heapName == null)
            heapName = HeapLDT.BASE_HEAP_NAME;

        clauses.computeIfAbsent(clause, it -> new ArrayList<>()).add(ctx);
        heaps.put(ctx, heapName);
        return this;
    }

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


    /**
     * Merge clauses of two spec cases.
     * Keep behavior of this one.
     *
     * @param other
     */
    public @NotNull TextualJMLSpecCase merge(@NotNull TextualJMLSpecCase other) {
        TextualJMLSpecCase res = clone();
        res.clauses.putAll(other.clauses);
        res.heaps.putAll(other.heaps);
        return res;
    }

    @Override
    public @NotNull TextualJMLSpecCase clone() {
        TextualJMLSpecCase res = new TextualJMLSpecCase(getMods(), getBehavior());
        res.name = name;
        res.clauses = new HashMap<>(clauses);
        return res;
    }

    public void addName(PositionedString n) {
        this.name = n.text;
        setPosition(n);
    }

    public Behavior getBehavior() {
        return behavior;
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return "TextualJMLSpecCase{" +
                "behavior=" + behavior +
                ", clauses=" + clauses +
                ", mods=" + mods +
                ", name='" + name + '\'' +
                '}';
    }


    /*
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<PositionedString> it;

        sb.append(behavior).append("\n");

        for (Triple<PositionedString, PositionedString, PositionedString> t : abbreviations) {
            sb.append("old: ");
            sb.append(t.first.toString());
            sb.append(" ");
            sb.append(t.second.toString());
            sb.append(" = ");
            sb.append(t.third.toString());
            sb.append("\n");
        }

        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = requires.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("requires<" + h + ">: " + it.next() + "\n");
            }
        }
        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = requiresFree.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("requires_free<" + h + ">: " + it.next() + "\n");
            }
        }
        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = assignables.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("assignable<" + h + ">: " + it.next() + "\n");
            }
        }
        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = accessibles.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("accessible<" + h + ">: " + it.next() + "\n");
            }
            it = accessibles.get(h.toString() + "AtPre").iterator();
            while (it.hasNext()) {
                sb.append("accessible<" + h + "AtPre>: " + it.next() + "\n");
            }
        }
        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = ensures.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("ensures<" + h + ">: " + it.next() + "\n");
            }
        }
        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = ensuresFree.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("ensures_free<" + h + ">: " + it.next() + "\n");
            }
        }
        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            it = axioms.get(h.toString()).iterator();
            while (it.hasNext()) {
                sb.append("axioms<" + h + ">: " + it.next() + "\n");
            }
        }
        it = signals.iterator();
        while (it.hasNext()) {
            sb.append("signals: ").append(it.next()).append("\n");
        }
        it = signalsOnly.iterator();
        while (it.hasNext()) {
            sb.append("signals_only: ").append(it.next()).append("\n");
        }
        it = diverges.iterator();
        while (it.hasNext()) {
            sb.append("diverges: ").append(it.next()).append("\n");
        }
        it = depends.iterator();
        while (it.hasNext()) {
            sb.append("depends: ").append(it.next()).append("\n");
        }
        it = breaks.iterator();
        while (it.hasNext()) {
            sb.append("breaks: ").append(it.next()).append("\n");
        }
        it = continues.iterator();
        while (it.hasNext()) {
            sb.append("continues: ").append(it.next()).append("\n");
        }
        it = returns.iterator();
        while (it.hasNext()) {
            sb.append("returns: ").append(it.next()).append("\n");
        }
        it = infFlowSpecs.iterator();
        while (it.hasNext()) {
            sb.append("determines: ").append(it.next()).append("\n");
        }
        return sb.toString();
    }
    */

    //region legacy api
    public void addAxioms(ParserRuleContext methodDefinition) {
    }

    public void addAssignable(ParserRuleContext positionedString) {
    }

    public void addRequires(ParserRuleContext label) {
        addClause(REQUIRES, label);
    }

    public void addSignals(PositionedLabeledString label) {
    }

    public void addDiverges(ParserRuleContext aTrue) {
    }

    public void addSignals(ParserRuleContext prepend) {
    }

    public void addEnsures(ParserRuleContext prepend) {
    }

    public void addRequires(ImmutableList<ParserRuleContext> precond) {
    }

    public Triple<ParserRuleContext, ParserRuleContext, ParserRuleContext>[] getAbbreviations() {
        return null;
    }

    public ImmutableList<ParserRuleContext> getInfFlowSpecs() {
        return getList(INFORMATION_FLOW);
    }

    public ImmutableList<ParserRuleContext> getReturns() {
        return getList(RETURNS);
    }

    public ImmutableList<ParserRuleContext> getContinues() {
        return getList(CONTINUES);
    }

    public ImmutableList<ParserRuleContext> getBreaks() {
        return getList(BREAKS);
    }

    public ImmutableList<ParserRuleContext> getDiverges() {
        return getList(DIVERGES);
    }

    public ImmutableList<ParserRuleContext> getMeasuredBy() {
        return getList(MEASURED_BY);
    }


    public void addEnsures(PositionedLabeledString ensures_) {
    }

    public void addSignalsOnly(PositionedString ctx) {

    }

    public ImmutableList<ParserRuleContext> getSignalsOnly() {
        return getList(SIGNALS_ONLY);
    }

    public ImmutableList<ParserRuleContext> getRequires() {
        return getList(REQUIRES);
    }

    private ImmutableList<ParserRuleContext> getList(Object key) {
        return ImmutableList.fromList(clauses.getOrDefault(key, new ArrayList<>()));
    }

    public ImmutableList<ParserRuleContext> getAssignable() {
        return getList(ASSIGNABLE);
    }

    public ImmutableList<ParserRuleContext> getEnsures() {
        return getList(ENSURES);
    }

    public ImmutableList<ParserRuleContext> getSignals() {
        return getList(SIGNALS);
    }
    //endregion

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TextualJMLSpecCase)) return false;
        TextualJMLSpecCase that = (TextualJMLSpecCase) o;
        return getBehavior() == that.getBehavior() &&
                clauses.equals(that.clauses);
    }

    @Override
    public int hashCode() {
        return Objects.hash(getBehavior(), clauses);
    }
}
