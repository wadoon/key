package de.uka.ilkd.key.rule.tuc;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.njml.JmlTermFactory;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class TucRuleApp extends AbstractBuiltInRuleApp {
    public static final Logger LOGGER = LoggerFactory.getLogger(TucRuleApp.class);

    final List<Goal> mergepartners = new ArrayList<>();
    Node ancestor;
    Function<List<Sequent>, Pair<ImmutableList<SequentFormula>, ImmutableList<SequentFormula>>> mergeFunction = TucRule.mtn;
    Goal goal;
    Pair<ImmutableList<SequentFormula>, ImmutableList<SequentFormula>> formulae;


    protected TucRuleApp(final BuiltInRule rule, final PosInOccurrence pio, final ImmutableList<PosInOccurrence> ifInsts) {
        super(rule, pio, ifInsts);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(final PosInOccurrence newPos) {
        final TucRuleApp app = new TucRuleApp(rule(), newPos, ifInsts);
        app.formulae = formulae;
        app.ancestor = ancestor;
        app.goal = goal;
        app.mergeFunction = mergeFunction;
        app.mergepartners.addAll(mergepartners);
        return app;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(final ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public boolean isSufficientlyComplete() {
        LOGGER.debug("tuc sufficent test");
        return true;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(final Goal goal) {
        LOGGER.debug("trying to instantiate TUC app");
        if (this.goal == goal) {
            // already instantiated ?
            return this;
        }
        if (ancestor == null) {
            var ref = new Object() {
                Node n = goal.node();
            };
            Node p = ref.n.parent();
            while (p != null && (p.childrenCount() == 1 || all(p.childrenIterator(), c -> (c == ref.n || c.isClosed())))) {
                ref.n = p;
                p = ref.n.parent();
            }
            if (p == null) {
                // failed: there is only one goal, so nothing to merge
                LOGGER.debug("ancestor search failed");
                return this;
            }
            assert any(p.childrenIterator(), c -> c != ref.n && !c.isClosed());
            ancestor = p;
        }
        LOGGER.debug("found ancestor {}", ancestor);

        this.goal = goal;
        mergepartners.clear();
        ArrayList<Node> leaves = new ArrayList<>();
        final Iterator<Node> it = ancestor.openLeavesIterator();
        while (it.hasNext()) {
            final Node n = it.next();
            leaves.add(n);
            if (n != goal.node()) {
                Goal g = goal.proof().getOpenGoal(n);
                mergepartners.add(g);
            }
        }
        this.formulae = mergeFunction.apply(leaves.stream().map(Node::sequent).collect(Collectors.toList()));

        if (pio == null) {
            if (!formulae.first.isEmpty()) {
                return replacePos(new PosInOccurrence(formulae.first.head(), PosInTerm.getTopLevel(), true));
            }
            if (!formulae.second.isEmpty()) {
                return replacePos(new PosInOccurrence(formulae.second.head(), PosInTerm.getTopLevel(), false));
            }
        }

        LOGGER.debug("found {} formulae", formulae.first.size() + formulae.second.size());
        LOGGER.debug("tuc completion status {} ({} {} {})", complete(), goal, formulae.first.isEmpty(), formulae.second.isEmpty());

        return this;
    }

    private static <T> boolean all(final Iterator<T> iterator, final Predicate<T> predicate) {
        while (iterator.hasNext()) {
            if (!predicate.test(iterator.next())) {
                return false;
            }
        }
        return true;
    }

    private static <T> boolean any(final Iterator<T> iterator, final Predicate<T> predicate) {
        while (iterator.hasNext()) {
            if (predicate.test(iterator.next())) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean complete() {
        return goal != null && !(formulae.first.isEmpty() && formulae.second.isEmpty());
    }
}
