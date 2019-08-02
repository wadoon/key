package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.interpreter.Interpreter;
import edu.kit.iti.formal.psdbg.parser.DefaultASTVisitor;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import edu.kit.iti.formal.psdbg.parser.ast.*;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import javax.annotation.Nonnull;
import javax.annotation.concurrent.ThreadSafe;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * This class listens to the interpreter and halts it, if a blocker is triggered.
 * <p>
 * Created by weigl on 21.05.2017.
 */
@NoArgsConstructor
public class HaltManager<T> implements InterpreterObserver<T> {
    private static Logger LOGGER = LogManager.getLogger(HaltManager.class);

    private final Lock lock = new ReentrantLock();
    private final Condition block = lock.newCondition();
    /**
     * Listeners, that are notify on blocking/continuing.
     */
    private final List<HaltListener> listeners = new LinkedList<>();
    @Getter
    @Setter
    private Interpreter<T> interpreter;
    @Getter
    private Visitor<Void> entryListener = new EntryListener();
    @Getter
    private Visitor<Void> exitListener = new ExitListener();

    private List<Blocker.BlockPredicate> predicates = new LinkedList<>();
    private Set<Blocker.BlockPredicate> markForRemoval = new HashSet<>();


    public HaltManager(@Nonnull Interpreter<T> inter) {
        install(inter);
    }

    public Void checkForHalt(ASTNode node) {
        boolean halt = false;
        List<Blocker.BlockPredicate> keep = new LinkedList<>();

        for (Blocker.BlockPredicate p : predicates) {
            if (p.test(node)) {
                LOGGER.debug("Blocked by {}", p);
                halt = true;
                if (!markForRemoval.contains(p)) {
                    keep.add(p);
                } else {
                    markForRemoval.remove(p);
                }
            } else {
                keep.add(p);
            }
        }
        predicates = keep;
        if (halt) {
            block();
        }

        return null;
    }

    private void fireContinue() {
        synchronized (listeners) {
            listeners.forEach(it -> it.onContinue(this.interpreter));
        }
    }

    private void fireHalt() {
        synchronized (listeners) {
            listeners.forEach(it -> it.onHalt(this.interpreter));
        }
    }

    public boolean addHaltListener(HaltListener haltListener) {
        synchronized (listeners) {
            return listeners.add(haltListener);
        }
    }

    public boolean removeHaltListener(HaltListener o) {
        synchronized (listeners) {
            return listeners.remove(o);
        }
    }

    /**
     * Blocks the current thread. Makes him awakable on {@code block}.
     */
    private void block() {
        fireHalt();
        try {
            lock.lock();
            block.await();
        } catch (InterruptedException e) {
            e.printStackTrace();
        } finally {
            lock.unlock();
        }
        fireContinue();
    }

    public void unlock() {
        try {
            lock.lock();
            block.signal();
        } finally {
            lock.unlock();
        }
    }

    public void deinstall() {
        deinstall(interpreter);
    }

    public void getMarkForDisable(Blocker.BlockPredicate predicate) {
        markForRemoval.add(predicate);
    }

    public synchronized void addPredicate(Blocker.BlockPredicate predicate) {
        predicates.add(predicate);
    }

    public synchronized void clearPredicates() {
        predicates.clear();
    }

    private class EntryListener extends DefaultASTVisitor<Void> {

        @Override
        public Void visit(ProofScript proofScript) {
            return checkForHalt(proofScript);
        }

        @Override
        public Void visit(AssignmentStatement assignment) {
            return checkForHalt(assignment);
        }


        @Override
        public Void visit(CasesStatement casesStatement) {
            return checkForHalt(casesStatement);
        }

        @Override
        public Void visit(CaseStatement caseStatement) {
            return checkForHalt(caseStatement);
        }

        @Override
        public Void visit(MatchExpression matchExpression) {
//           System.out.println("Checkforhalt matchexpression");
            return checkForHalt(matchExpression);
        }

        @Override
        public Void visit(CallStatement call) {
            //          System.out.println("Checkforhalt callstatement");
            return checkForHalt(call);
        }

        @Override
        public Void visit(GuardedCaseStatement guardedCaseStatement) {
            return checkForHalt(guardedCaseStatement);
        }

        @Override
        public Void visit(TheOnlyStatement theOnly) {
            return checkForHalt(theOnly);
        }

        @Override
        public Void visit(ForeachStatement foreach) {
            return checkForHalt(foreach);
        }

        @Override
        public Void visit(RepeatStatement repeatStatement) {
            return checkForHalt(repeatStatement);
        }
    }

    private class ExitListener extends DefaultASTVisitor<Void> {

    }
}
