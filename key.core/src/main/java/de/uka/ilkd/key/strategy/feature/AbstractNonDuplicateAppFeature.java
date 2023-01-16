package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.AssertionFailure;
import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;

import java.util.*;


public abstract class AbstractNonDuplicateAppFeature extends BinaryTacletAppFeature {
    private static final ThreadLocal<LRUCache<Node, HashMap<Name, List<RuleApp>>>> localCache =
        ThreadLocal.withInitial(() -> new LRUCache<>(32));

    protected AbstractNonDuplicateAppFeature() {}

    /**
     * Compare whether two <code>PosInOccurrence</code>s are equal. This can be done using
     * <code>equals</code> or <code>eqEquals</code> (checking for same or equal formulas), which has
     * to be decided by the subclasses
     */
    protected abstract boolean comparePio(TacletApp newApp, TacletApp oldApp,
            PosInOccurrence newPio, PosInOccurrence oldPio);

    /**
     * Check whether a semisequent contains a formula. Again, one can either search for the same or
     * an equal formula
     */
    protected abstract boolean semiSequentContains(Semisequent semisequent, SequentFormula cfma);

    /**
     * Gets rule apps applied to any node before the given node with the given name.
     *
     * Multiple assumptions about nodes:
     * * The given node is a leaf, no children, no applied rule
     * * Only *new* nodes are appended to nodes
     * * Non leaf nodes are not changed, pruning is allowed
     * * If the tree is pruned the removed nodes are discarded and not reused
     *
     * @param node the node
     * @param name the name
     * @return rule apps
     */
    public static List<RuleApp> getRuleAppsWithName(Node node, Name name) {
        if (node.getAppliedRuleApp() != null || node.childrenCount() != 0) {
            throw new AssertionFailure("Expected an empty leaf node");
        }
        final var cacheValue = localCache.get();
        HashMap<Name, List<RuleApp>> cache = cacheValue.get(node);

        if (cache == null) {
            // Try to use parent cache to initialize the new cache
            HashMap<Name, List<RuleApp>> parentCache =
                node.root() ? null : cacheValue.get(node.parent());
            cache = new HashMap<>();

            if (parentCache != null) {
                if (node.parent().childrenCount() <= 1) {
                    // Parent cache will be removed, reuse it
                    cache = parentCache;
                } else {
                    // Copy the parent cache
                    for (Map.Entry<Name, List<RuleApp>> entry : parentCache.entrySet()) {
                        cache.put(entry.getKey(), new ArrayList<>(entry.getValue()));
                    }
                }

                // Parent did not have a rule applied when we calculated this, add the rule applied
                // there
                RuleApp parentApp = node.parent().getAppliedRuleApp();
                cache.computeIfAbsent(parentApp.rule().name(), k -> new ArrayList<>())
                        .add(parentApp);

                // If this is an inner node, we hope we will never revisit it, remove it from the
                // cache
                if (node.parent().childrenCount() <= 1) {
                    cacheValue.remove(node.parent());
                }
            } else {
                // Check all earlier rule applications
                Node current = node;
                while (!current.root()) {
                    final Node par = current.parent();

                    RuleApp a = par.getAppliedRuleApp();
                    cache.computeIfAbsent(a.rule().name(), k -> new ArrayList<>()).add(a);

                    current = par;
                }
            }

            cacheValue.put(node, cache);
        }

        List<RuleApp> apps = cache.get(name);
        return apps == null ? null : Collections.unmodifiableList(apps);
    }

    /**
     * Check whether the old rule application <code>ruleCmp</code> is a duplicate of the new
     * application <code>newApp</code> at position <code>newPio</code>.<code>newPio</code> can be
     * <code>null</code>
     */
    protected boolean sameApplication(RuleApp ruleCmp, TacletApp newApp, PosInOccurrence newPio) {
        // compare the rules
        if (newApp.rule() != ruleCmp.rule()) {
            return false;
        }

        final TacletApp cmp = (TacletApp) ruleCmp;

        // compare the position of application
        if (newPio != null) {
            if (!(cmp instanceof PosTacletApp))
                return false;
            final PosInOccurrence oldPio = cmp.posInOccurrence();
            if (!comparePio(newApp, cmp, newPio, oldPio))
                return false;
        }


        // compare the if-sequent instantiations
        final ImmutableList<IfFormulaInstantiation> newAppIfFmlInstantiations =
            newApp.ifFormulaInstantiations();
        final ImmutableList<IfFormulaInstantiation> cmpIfFmlInstantiations =
            cmp.ifFormulaInstantiations();
        if (newAppIfFmlInstantiations == null || cmpIfFmlInstantiations == null) {
            if (newAppIfFmlInstantiations != null || cmpIfFmlInstantiations != null) {
                return false;
            }
        } else {

            final Iterator<IfFormulaInstantiation> it0 = newAppIfFmlInstantiations.iterator();
            final Iterator<IfFormulaInstantiation> it1 = cmpIfFmlInstantiations.iterator();

            while (it0.hasNext()) {
                // this test should be improved
                if (it0.next().getConstrainedFormula() != it1.next().getConstrainedFormula())
                    return false;
            }
        }

        return equalInterestingInsts(newApp.instantiations(), cmp.instantiations());
    }

    private boolean equalInterestingInsts(SVInstantiations inst0, SVInstantiations inst1) {
        if (!inst0.getUpdateContext().equals(inst1.getUpdateContext()))
            return false;

        final ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting0 =
            inst0.interesting();
        final ImmutableMap<SchemaVariable, InstantiationEntry<?>> interesting1 =
            inst1.interesting();
        return subset(interesting0, interesting1) && subset(interesting1, interesting0);
    }

    private boolean subset(ImmutableMap<SchemaVariable, InstantiationEntry<?>> insts0,
            ImmutableMap<SchemaVariable, InstantiationEntry<?>> insts1) {
        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it =
            insts0.iterator();

        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry0 = it.next();

            if (entry0.key() instanceof SkolemTermSV || entry0.key() instanceof VariableSV)
                continue;

            final InstantiationEntry<?> instEntry1 = insts1.get(entry0.key());

            if (instEntry1 == null
                    || !entry0.value().getInstantiation().equals(instEntry1.getInstantiation()))
                return false;
        }

        return true;
    }

    /**
     * Search for a duplicate of the application <code>app</code> by walking upwards in the proof
     * tree. Here, we assume that <code>pos</code> is non-null, and as an optimisation we stop as
     * soon as we have reached a point where the formula containing the focus no longer occurs in
     * the sequent
     */
    protected boolean noDuplicateFindTaclet(TacletApp app, PosInOccurrence pos, Goal goal) {
        final Node node = goal.node();
        List<RuleApp> apps = getRuleAppsWithName(node, app.rule().name());
        if (apps == null) {
            return true;
        }

        // Check all rules with this name
        for (RuleApp a : apps) {
            if (sameApplication(a, app, pos))
                return false;
        }

        return true;
    }

}
