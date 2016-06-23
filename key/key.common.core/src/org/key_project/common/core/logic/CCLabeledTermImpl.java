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

package org.key_project.common.core.logic;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * The labeled term class is used for terms that have a label attached.
 * <p>
 * Two labeled terms are equal if they have equal term structure and equal
 * annotations. In contrast the method {@link Term#equalsModRenaming(Object)}
 * does not care about annotations and will just compare the term structure
 * alone modulo renaming.
 * 
 * @see Term
 * @see TermImpl
 */
public abstract class CCLabeledTermImpl<P extends ModalContent, V extends CCTermVisitor<T>, T extends CCTerm<P,V,T>> extends CCTermImpl<P,V,T> {

    private final ImmutableArray<TermLabel> labels;

    /**
     * creates an instance of a labeled term.
     * 
     * @param op
     *            the top level operator
     * @param subs
     *            the Term that are the subterms of this term
     * @param boundVars
     *            logic variables bound by the operator
     * @param javaBlock
     *            contains the program part of the term (if any)
     * @param labels
     *            the terms labels (must not be null or empty)
     */
    public CCLabeledTermImpl(Operator op, Sort sort, ImmutableArray<T> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            P javaBlock,
            ImmutableArray<TermLabel> labels) {
        super(op, sort, subs, boundVars, javaBlock);
        assert labels != null : "Term labels must not be null";
        assert !labels.isEmpty() : "There must be at least one term label";
        this.labels = labels;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasLabels() {
        return true;
    }

    /**
     * returns the labels attached to this term
     */
    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return labels;
    }

    @Override
    public TermLabel getLabel(final Name termLabelName) {
        return CollectionUtil.search(labels, new IFilter<TermLabel>() {
            @Override
            public boolean select(TermLabel element) {
                return ObjectUtil.equals(element.name(), termLabelName);
            }
        });
    }

    /**
     * returns true if the given label is attached
     * 
     * @param label
     *            the TermLabel for which to look (must not be null)
     * @return true iff. the label is attached to this term
     */
    @Override
    public boolean containsLabel(TermLabel label) {
        assert label != null : "Label must not be null";
        for (int i = 0, sz = labels.size(); i < sz; i++) {
            if (label.equals(labels.get(i))) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object o) {
        if (!super.equals(o)) {
            return false;
        }

        @SuppressWarnings("unchecked")
        final CCLabeledTermImpl<P, V, T> cmp = (CCLabeledTermImpl<P, V, T>) o;
        if (labels.size() == cmp.labels.size()) {
            for (int i = 0, sz = labels.size(); i < sz; i++) {
                // this is not optimal, but as long as number of labels limited
                // ok
                if (!cmp.labels.contains(labels.get(i))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int computeHashCode() {
        int hash = super.computeHashCode();
        for (int i = 0, sz = labels.size(); i < sz; i++) {
            hash += 7 * labels.get(i).hashCode();
        }
        return hash;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder result = new StringBuilder(super.toString());
        result.append("<<");
        // as labels must not be empty at least one element exists
        result.append(labels.get(0).toString());
        for (int i = 1; i < labels.size(); i++) {
            result.append(", ");
            result.append(labels.get(i).toString());
        }
        result.append(">>");
        return result.toString();
    }
}