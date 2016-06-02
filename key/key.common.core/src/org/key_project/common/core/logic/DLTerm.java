package org.key_project.common.core.logic;

import org.key_project.common.core.logic.op.DLQuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

public interface DLTerm<S extends DLSort, V extends DLVisitor<? extends DLTerm<S,V>>> {

    /** 
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f").
     */
    public DLOperator<S, ? extends DLTerm<S, V>> op();

    /** 
     * The <code>n</code>-th direct subterm.
     */
    public DLTerm<S,V> sub(int n);

    /**
     * The subterms.
     */
    public ImmutableArray<? extends DLTerm<S, V>> subs();

    /**
     * The arity of the term.   
     * */
    public int arity();

    /**
     * The nesting depth of this term.
     */
    public int depth();
    
    /**
     * Whether all operators in this term are rigid.
     */
    public boolean isRigid();
    
    /** 
     * The visitor is handed through till the bottom of the tree and
     * then it walks upwards, while at each upstep the method visit of
     * the visitor is called.
     * @param visitor the Visitor
     */
    public void execPostOrder(V visitor);

    /** 
     * The visitor walks downwards the tree, while at each downstep the method 
     * visit of the visitor is called.
     * @param visitor the Visitor
     */
    public void execPreOrder(V visitor);

    /** 
     * The set of free quantifiable variables occurring in this term.
     */
    public ImmutableSet<? extends DLQuantifiableVariable<S, ? extends DLTerm<S, V>>> freeVars();
    
    /**
    * The logical variables bound by the top level operator.
    */
   public ImmutableArray<? extends DLQuantifiableVariable<S, ? extends DLTerm<S, V>>> boundVars();

   /**
    * The logical variables bound by the top level operator for the nth 
    * subterm.
    */
   public ImmutableArray<? extends DLQuantifiableVariable<S, ? extends DLTerm<S, V>>> varsBoundHere(int n);


}
