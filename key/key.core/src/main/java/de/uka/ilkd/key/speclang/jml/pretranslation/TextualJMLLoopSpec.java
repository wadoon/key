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
import de.uka.ilkd.key.njml.LabeledParserRuleContext;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.*;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ASSIGNABLE;


/**
 * A JML loop specification (invariant, assignable clause, decreases
 * clause, ...) in textual form.
 */
public final class TextualJMLLoopSpec extends TextualJMLConstruct {
    private LabeledParserRuleContext variant = null;

    public enum Clause {
        INFORMATION_FLOW
    }

    /**
     * Heap-dependent clauses
     */
    public enum ClauseHd {
        ASSIGNABLE,
        INVARIANT,
        INVARIANT_FREE
    }

    private Map<Object, List<LabeledParserRuleContext>> clauses = new HashMap<>();
    private Map<LabeledParserRuleContext, Name> heaps = new HashMap<>();

    public TextualJMLLoopSpec(ImmutableList<String> mods) {
        super(mods);
    }

    public TextualJMLLoopSpec addClause(Clause clause, LabeledParserRuleContext ctx) {
        clauses.computeIfAbsent(clause, it -> new ArrayList<>()).add(ctx);
        return this;
    }

    public TextualJMLLoopSpec addClause(ClauseHd clause, LabeledParserRuleContext ctx) {
        return addClause(clause, null, ctx);
    }

    public TextualJMLLoopSpec addClause(ClauseHd clause, @Nullable Name heapName, LabeledParserRuleContext ctx) {
        if (heapName == null)
            heapName = HeapLDT.BASE_HEAP_NAME;

        clauses.computeIfAbsent(clause, it -> new ArrayList<>()).add(ctx);
        heaps.put(ctx, heapName);
        return this;
    }

    public void setVariant(LabeledParserRuleContext ps) {
        assert variant == null;
        variant = ps;
        setPosition(ps);
    }

    private ImmutableList<LabeledParserRuleContext> getList(Object key) {
        return ImmutableList.fromList(clauses.getOrDefault(key, new ArrayList<>()));
    }

    public ImmutableList<LabeledParserRuleContext> getAssignable() {
        return getList(ASSIGNABLE);
    }

    /*public ImmutableList<LabeledParserRuleContext> getAssignable(String hName) {
        return getList(ClauseHd.ASSIGNABLE);
    }*/

    public Map<String, ImmutableList<LabeledParserRuleContext>> getAssignables() {
        return getMap(ClauseHd.ASSIGNABLE);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getAssignablesInit() {
        return getMapInit(ClauseHd.ASSIGNABLE);
    }


    public ImmutableList<LabeledParserRuleContext> getInfFlowSpecs() {
        return getList(Clause.INFORMATION_FLOW);
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getInvariants() {
        return getMap(ClauseHd.INVARIANT);
    }

    private Map<String, ImmutableList<LabeledParserRuleContext>> getMapInit(ClauseHd clause) {
        ImmutableList<LabeledParserRuleContext> seq = getList(clause);
        Name defaultHeap = HeapLDT.BASE_HEAP_NAME;
        Map<String, ImmutableList<LabeledParserRuleContext>> map = new HashMap<>();
        for (LabeledParserRuleContext context : seq) {
            String h = heaps.getOrDefault(context, defaultHeap).toString();
            ImmutableList<LabeledParserRuleContext> l = map.getOrDefault(h, ImmutableSLList.nil());
            map.put(h, l.append(context));
        }

        for (Name h : HeapLDT.VALID_HEAP_NAMES) {
            if (!map.containsKey(h.toString())) {
                map.put(h.toString(), ImmutableSLList.nil());
            }
        }
        return map;
    }

    private Map<String, ImmutableList<LabeledParserRuleContext>> getMap(ClauseHd clause) {
        ImmutableList<LabeledParserRuleContext> seq = getList(clause);
        Name defaultHeap = HeapLDT.BASE_HEAP_NAME;
        Map<String, ImmutableList<LabeledParserRuleContext>> map = new HashMap<>();
        for (LabeledParserRuleContext context : seq) {
            String h = heaps.getOrDefault(context, defaultHeap).toString();
            ImmutableList<LabeledParserRuleContext> l = map.getOrDefault(h, ImmutableSLList.nil());
            map.put(h, l.append(context));
        }
        return map;
    }

    public Map<String, ImmutableList<LabeledParserRuleContext>> getFreeInvariants() {
        return getMap(ClauseHd.INVARIANT_FREE);
    }

    public LabeledParserRuleContext getVariant() {
        return variant;
    }

    /*@Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<LabeledParserRuleContext> it;

        for (Name heap : HeapLDT.VALID_HEAP_NAMES) {
            it = invariants.get(heap.toString()).iterator();
            while (it.hasNext()) {
                sb.append("invariant<" + heap + ">: " + it.next() + "\n");
            }
        }
        for (Name heap : HeapLDT.VALID_HEAP_NAMES) {
            it = freeInvariants.get(heap.toString()).iterator();
            while (it.hasNext()) {
                sb.append("free invariant<" + heap + ">: " + it.next() + "\n");
            }
        }
        for (Name heap : HeapLDT.VALID_HEAP_NAMES) {
            it = assignables.get(heap.toString()).iterator();
            while (it.hasNext()) {
                sb.append("assignable<" + heap + ">: " + it.next() + "\n");
            }
        }
        for (Name heap : HeapLDT.VALID_HEAP_NAMES) {
            it = infFlowSpecs.iterator();
            while (it.hasNext()) {
                sb.append("determines<" + heap + ">: " + it.next() + "\n");
            }
        }
        if (variant != null) {
            sb.append("decreases: " + variant);
        }

        return sb.toString();
    }
       */


    @Override
    public String toString() {
        return "TextualJMLLoopSpec{" +
                "variant=" + variant +
                ", clauses=" + clauses +
                ", heaps=" + heaps +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        TextualJMLLoopSpec that = (TextualJMLLoopSpec) o;
        return variant.equals(that.variant) &&
                clauses.equals(that.clauses) &&
                heaps.equals(that.heaps);
    }

    @Override
    public int hashCode() {
        return Objects.hash(variant, clauses, heaps);
    }
}
