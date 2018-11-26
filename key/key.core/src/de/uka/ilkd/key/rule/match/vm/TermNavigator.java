package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayDeque;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.logic.Term;

/**
 * An iterator that walks in first-depth order through the term. It allows to jump to siblings.
 */
public class TermNavigator {
    
    
    private static final int POOL_SIZE = 100;
    private static ReentrantLock TERM_NAVIGATOR_POOL_WRITE_LOCK = new ReentrantLock();

    /** 
     * TERM_NAVIGATOR_POOL of TermNavigator as these are created very often and short-living
     * we reuse them as far as possible 
     * 
     * The used TermNavigator have to be explicitly released by the user via {@link #release()}
     */
    private static ArrayDeque<TermNavigator> TERM_NAVIGATOR_POOL = new ArrayDeque<>();
    static {
        for (int i = 0; i<POOL_SIZE; i++) {
            TERM_NAVIGATOR_POOL.push(new TermNavigator());
        }
    }

    /**
     * returns a pooled {@link TermNavigator} or a new one if the TERM_NAVIGATOR_POOL is currently empty
     * The used TermNavigator have to be explicitly released by the user via {@link #release()}
     * @return a pooled {@link TermNavigator} or a new one if the TERM_NAVIGATOR_POOL is currently empty
     */
    public static TermNavigator get(Term term) {
        TermNavigator tn = null;
        if (TERM_NAVIGATOR_POOL_WRITE_LOCK.tryLock()) {
            if (!TERM_NAVIGATOR_POOL.isEmpty()) {
                tn = TERM_NAVIGATOR_POOL.pop();
            }
            TERM_NAVIGATOR_POOL_WRITE_LOCK.unlock();
        }
        if (tn != null) {
            tn.stack.push(MutablePair.get(term, 0));
        } else { 
            tn = new TermNavigator(term);
        }
        return tn;
    }
    

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
    private final ArrayDeque<MutablePair> stack = new ArrayDeque<>();
    
    private TermNavigator() {
    }

    private TermNavigator(Term term) {
        stack.push(MutablePair.get(term, 0));
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
            MutablePair el = stack.peek();            
            if (el.second < el.first.arity()) {
                final int oldPos = el.second;
                final Term oldTerm = el.first;
                el.second += 1;
                if (el.second >= oldTerm.arity()) {
                    // we visited all children of that term
                    // so it can be removed from the stack
                    stack.pop().release(); // el's components are set to null 
                }
                el = MutablePair.get(oldTerm.sub(oldPos), 0);
                stack.push(el);
            } else {
                stack.pop().release();
            }
        } while (!stack.isEmpty() && stack.peek().second != 0);
    }
    
    public void gotoNext() {
        gotoNextHelper();
    }
    
    public void gotoNextSibling() {
        stack.pop().release();;
        gotoNextHelper();            
    }
    
    public void release() {
        stack.forEach((e)->e.release());
        stack.clear();
        if (TERM_NAVIGATOR_POOL.size() < POOL_SIZE) {
            if (TERM_NAVIGATOR_POOL_WRITE_LOCK.tryLock()) {
                TERM_NAVIGATOR_POOL.push(this);
                TERM_NAVIGATOR_POOL_WRITE_LOCK.unlock();
            }
        }
    }


    /** 
     * A mutable tuple of two types
     */
    private static class MutablePair {
        
        private static final int PAIR_POOL_SIZE = 1000;

        private static ReentrantLock PAIR_POOL_WRITE_LOCK = new ReentrantLock();
        
        
        /** 
         * TERM_NAVIGATOR_POOL of TermNavigator.MutablePair as these are created very often and short-living
         * we reuse them as far as possible 
         * 
         * The used TermNavigator have to be explicitly released by the user via {@link #release()}
         */
        private static ArrayDeque<MutablePair> PAIR_POOL = new ArrayDeque<>();
        static {
            for (int i = 0; i<PAIR_POOL_SIZE; i++) {
                PAIR_POOL.push(new MutablePair(null,null));
            }
        }
        /**
         * returns a pooled {@link MutablePair} or a new one if the TERM_NAVIGATOR_POOL is currently empty
         * The used MutablePair have to be explicitly released by the user via {@link #release()}
         * @return a pooled {@link MutablePair} or a new one if the TERM_NAVIGATOR_POOL is currently empty
         */
        static MutablePair get(Term first, Integer second) {
            MutablePair pair = null;

            if ( PAIR_POOL_WRITE_LOCK.tryLock() ) {
                if (!PAIR_POOL.isEmpty()) {
                    pair = PAIR_POOL.pop();
                }
                PAIR_POOL_WRITE_LOCK.unlock();
            }
            
            if (pair != null) {
                pair.first = first;
                pair.second = second;
            } else {
                pair = new MutablePair(first, second);
            }
            return pair;
        }
        

        /**
         *  first component of the pair
         */
        Term first;
        /**
         *  second component of the pair
         */
        Integer second;
        
        /**
         * creates an instance of a mutable pair
         * 
         * @param first  the first component of the pair
         * @param second the second component of the pair
         */
        public MutablePair(Term first, Integer second) {
            this.first = first;
            this.second = second;
        }
        
        /**
         * instances of this class managed by a pool
         * this method releases them to the pool 
         */
        public final void release() {
            first = null;
            second = null;
            if (PAIR_POOL_WRITE_LOCK.tryLock()) {
                if (PAIR_POOL.size() < PAIR_POOL_SIZE) {
                    PAIR_POOL.push(this);
                }
                PAIR_POOL_WRITE_LOCK.unlock();
            }
        }
        
        @Override
        public String toString() {
            return "MutablePair [first=" + first + ", second=" + second
                    + "]";
        }
    }
    
}