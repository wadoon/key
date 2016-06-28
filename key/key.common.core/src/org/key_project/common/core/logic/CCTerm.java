// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.logic;

import org.key_project.common.core.logic.factories.CCTermFactory;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SVSubstitute;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.logic.visitors.CCTermVisitor;
import org.key_project.common.core.program.CCSourceElement;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/** 
 * In contrast to the distinction of formulas and terms as made by most of the 
 * inductive definitions of the syntax of a logic, an instance of this class can
 * stand for a term or a formula. This is done for implementation reasons, as
 * their structure is quite similar and there are good reasons concerning the
 * software's design/architecture (for example using same visitors, reduction of
 * case distinction, unified interfaces etc.). However, they are strictly
 * separated by their sorts. A formula (and just a formula) must have 
 * the sort {@link Sort#FORMULA}. Terms of a different sort are terms in the
 * customary logic sense. A term of sort formula is allowed exact there, where a
 * formuala in logic is allowed to appear, same for terms of different sorts. 
 *   Some words about other design decisions: 
 * <ol> 
 *  <li> terms are immutable, this means after a term object is created, it
 *  cannot be changed. The advantage is that we can use term sharing and
 *  saving a lot of memory space. 
 *  </li>
 *  <li> Term has to be created using the {@link CCTermFactory} and
 *    <emph>not</emph> by using the constructors itself. 
 *  </li>
 *  <li> Term is subclassed, but all subclasses have to be package private, so
 *    that all other classes except {@link CCTermFactory} know only the class
 *    Term and its interface. Even most classes of the logic package.
 *  </li>
 *  <li> as it is immutable, most (all) attributes should be declared final
 * </li>
 * </ol>
 * Term supports the {@link CCTermVisitor} pattern. Two different visit strategies are
 * currently supported: {@link Term#execPostOrder(CCTermVisitor)} and
 * {@link Term#execPreOrder(CCTermVisitor)}.
 */
public interface CCTerm<S extends CCSourceElement<?, S>, P extends ModalContent<S>, V extends CCTermVisitor<T>, T extends CCTerm<?, P, V, T>>
        extends SVSubstitute, Sorted {

    /** 
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f").
     */
    Operator op();

    /**
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f")
     * casted to the passed type.
     */
    <O> O op(Class<O> opClass) throws IllegalArgumentException;

    
    /**
     * The modal content 
     */
    public P modalContent();

    /**
     * Checks if the {@link ModalContent} or one of its direct or indirect children
     * contains a non empty {@link ModalContent}.
     * 
     * @return {@code true} The {@link ModalContent} or one of its direct or indirect
     *         children contains a non empty {@link ModalContent}, {@code false} no
     *         {@link ModalContent} available.
     */
    public boolean containsModalContentRecursive();

    
    /**
     * The subterms.
     */
    ImmutableArray<T> subs();

    /** 
     * The <code>n</code>-th direct subterm.
     */
    T sub(int n);

    /**
     * The logical variables bound by the top level operator.
     */
    ImmutableArray<QuantifiableVariable> boundVars();

    /**
     * The logical variables bound by the top level operator for the nth 
     * subterm.
     */
    ImmutableArray<QuantifiableVariable> varsBoundHere(int n);

    /**
     * The arity of the term.   
     * */
    int arity();

    /**
     * The sort of the term.
     */
    Sort sort();

    /**
     * The nesting depth of this term.
     */
    int depth();

    /**
     * Whether all operators in this term are rigid.
     */
    boolean isRigid();

    /** 
     * The set of free quantifiable variables occurring in this term.
     */
    ImmutableSet<QuantifiableVariable> freeVars();

    /** 
     * The visitor is handed through till the bottom of the tree and
     * then it walks upwards, while at each upstep the method visit of
     * the visitor is called.
     * @param visitor the Visitor
     */
    void execPostOrder(V visitor);

    /** 
     * The visitor walks downwards the tree, while at each downstep the method 
     * visit of the visitor is called.
     * @param visitor the Visitor
     */
    void execPreOrder(V visitor);

    /**
     * Compares if two terms are equal modulo bound renaming
     * 
     * @return true iff (1) o is of the same Term type, and (2) the given Term
     *         has the same values in operator, sort, arity, varsBoundHere and
     *         javaBlock as this object modulo bound renaming
     */
    boolean equalsModRenaming(Object o);

    /**
     * returns true if the term is labeled
     */
    boolean hasLabels();

    /**
     * checks if the given label is attached to the term
     * @param label the TermLabel for which to look (must not be null)
     */
    boolean containsLabel(TermLabel label);

    /**
     * returns list of labels attached to this term
     * @return list of labels (maybe be empty but never <code>null</code>
     */
    ImmutableArray<TermLabel> getLabels();

    /**
     * Returns the first {@link TermLabel} with the given {@link Name}.
     * @param termLabelName The {@link Name} of the {@link TermLabel} to search.
     * @return The first found {@link TermLabel} or {@code null} if not available.
     */
    TermLabel getLabel(Name termLabelName);

    /**
     * Returns a serial number for a term. The serial number is not persistent.
     */
    int serialNumber();

}