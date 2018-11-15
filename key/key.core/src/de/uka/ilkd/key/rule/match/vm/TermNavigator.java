package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayDeque;
import java.util.Deque;

import de.uka.ilkd.key.logic.Term;

/**
 * An iterator that walks in first-depth order through the term. It allows to jump to siblings.
 */
public class TermNavigator {

    /** 
     * top element on stack contains always the pair whose
     * first component is the element to be returned by 
     * {@link #next()} while the second points to the child to 
     * be visited next (or equals the arity of the first component 
     * if no such child exists)
     * For all elements on the stack that are not the top element
     * the second component is less than the arity of the term in the 
     * first component
     */
    private final Deque<TermNavigator.MutablePair<Term,Integer>> stack = new ArrayDeque<>();
    
    public TermNavigator(Term term) {
        stack.push(new TermNavigator.MutablePair<Term,Integer>(term, 0));
    }
    
    public boolean hasNext() {
        return !stack.isEmpty();
    }

    public boolean hasNextSibling() {
        return stack.size() > 1;
    }

    
    public Term getCurrentSubterm() {
        return stack.peek().first; 
    }
    
    private /*@ helper @*/ void gotoNextHelper() { 
        if (stack.isEmpty()) {
            return;
        }
        do {
            TermNavigator.MutablePair<Term, Integer> el = stack.peek();            
            if (el.second < el.first.arity()) {
                final int oldPos = el.second;
                el.second += 1;
                if (el.second >= el.first.arity()) {
                    // we visited all children of that term
                    // so it can be removed from the stack
                    stack.pop();
                }
                el = new TermNavigator.MutablePair<Term, Integer>(el.first.sub(oldPos), 0);
                stack.push(el);
            } else {
                stack.pop();  
            }
        } while (!stack.isEmpty() && stack.peek().second != 0);
    }
    
    public void gotoNext() {
        gotoNextHelper();
    }
    
    public void gotoNextSibling() {
        stack.pop();
        gotoNextHelper();            
    }

    /** 
     * A mutable tuple of two types
     * @param <Fst> the type of the first component of the tuple
     * @param <Snd> the type of the second component of the tuple
     */
    static class MutablePair<Fst,Snd> {
        final Fst first;
        Snd second;
        
        public MutablePair(Fst first, Snd second) {
            this.first = first;
            this.second = second;
        }

        @Override
        public String toString() {
            return "MutablePair [first=" + first + ", second=" + second
                    + "]";
        }
    }
    
}