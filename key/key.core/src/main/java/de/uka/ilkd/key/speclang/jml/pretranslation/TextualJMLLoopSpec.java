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
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;


/**
 * A JML loop specification (invariant, assignable clause, decreases
 * clause, ...) in textual form.
 */
public final class TextualJMLLoopSpec extends TextualJMLSpecCase {
    private ParserRuleContext variant = null;

    public TextualJMLLoopSpec(ImmutableList<String> mods) {
        super(mods, Behavior.BEHAVIOR);
    }


    public void addInvariant(ParserRuleContext ps) {
        addGeneric(invariants, ps);
    }

    public void addFreeInvariant(ParserRuleContext ps) {
        addGeneric(freeInvariants, ps);
    }

    public void addAssignable(ParserRuleContext ps) {
        addGeneric(assignables, ps);
    }

    public void addInfFlowSpecs(ParserRuleContext ps) {
        infFlowSpecs = infFlowSpecs.append(ps);
    }

    public void addInfFlowSpecs(ImmutableList<ParserRuleContext> l) {
        infFlowSpecs = infFlowSpecs.append(l);
    }

    public void setVariant(ParserRuleContext ps) {
        assert variant == null;
        variant = ps;
        setPosition(ps);
    }

    public ImmutableList<ParserRuleContext> getAssignable() {
        return assignables.get(HeapLDT.BASE_HEAP_NAME.toString());
    }

    public ImmutableList<ParserRuleContext> getAssignable(String hName) {
        return assignables.get(hName);
    }

    public Map<String, ImmutableList<ParserRuleContext>> getAssignables() {
        return assignables;
    }

    public ImmutableList<ParserRuleContext> getInfFlowSpecs() {
        return infFlowSpecs;
    }

    public Map<String, ImmutableList<ParserRuleContext>> getInvariants() {
        return invariants;
    }

    public Map<String, ImmutableList<ParserRuleContext>> getFreeInvariants() {
        return freeInvariants;
    }

    public ParserRuleContext getVariant() {
        return variant;
    }


    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator<ParserRuleContext> it;

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


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLLoopSpec)) {
            return false;
        }
        TextualJMLLoopSpec ls = (TextualJMLLoopSpec) o;
        return mods.equals(ls.mods)
                && invariants.equals(ls.invariants)
                && assignables.equals(ls.assignables)
                && infFlowSpecs.equals(ls.infFlowSpecs)
                && (variant == null && ls.variant == null
                || variant != null && variant.equals(ls.variant));
    }

    @Override
    public int hashCode() {
        return mods.hashCode()
                + invariants.hashCode()
                + assignables.hashCode()
                + infFlowSpecs.hashCode();
    }
}
