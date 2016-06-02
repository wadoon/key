package org.key_project.common.core.logic;

import org.key_project.util.collection.ImmutableArray;

public interface DLTerm<V extends DLVisitor<? extends DLTerm<V>>> {

    
    /** 
     * The <code>n</code>-th direct subterm.
     */
    public DLTerm<V> sub(int n);

    /**
     * The subterms.
     */
    public ImmutableArray<? extends DLTerm<V>> subs();

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

}
