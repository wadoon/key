package de.tud.cs.se.ds.psec.compiler.ast;

import java.util.HashMap;
import java.util.Optional;

import de.tud.cs.se.ds.psec.util.Utilities;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates instantiations of {@link SchemaVariable}s in {@link TacletApp}s,
 * or matched constructs in {@link BuiltInRule} applications.
 *
 * @author Dominic Scheurer
 */
public class RuleInstantiations {

    private HashMap<String, Object> instantiations = new HashMap<>();

    /**
     * @param instantiations
     *            The instantiations of {@link SchemaVariable}s (mapping of
     *            {@link SchemaVariable} names to instantiations) or constructs
     *            in {@link BuiltInRule} apps (mapping of fixed identifiers to
     *            instantiations)
     */
    public RuleInstantiations(HashMap<String, Object> instantiations) {
        this.instantiations = instantiations;
    }

    /**
     * Creates {@link RuleInstantiations} for a given {@link TacletApp} by
     * iterating over all {@link SchemaVariable}s and retrieving the
     * instantiated values.
     * 
     * @param app
     *            The {@link TacletApp} to retrieve instantiations from.
     */
    public RuleInstantiations(final TacletApp app) {
        if (app == null || app.instantiations() == null) {
            return;
        }
        
        (Utilities.toStream(() -> app.instantiations().svIterator()))
                .map(SchemaVariable::name)
                .map(svName -> new Pair<>(svName.toString(),
                        app.instantiations().lookupValue(svName)))
                .filter(pair -> pair.second != null)
                .forEach(pair -> instantiations.put(pair.first, pair.second));
    }

    /**
     * Returns the instantiation corresponding to the given key <code>sv</code>.
     * 
     * @param sv
     *            The name for {@link SchemaVariable} / {@link BuiltInRule}
     *            construct.
     * @return The instantiation for <code>sv</code>, if any, or an
     *         {@link Optional#empty()}.
     */
    public Optional<Object> getInstantiationFor(String sv) {
        if (instantiations.containsKey(sv)) {
            return Optional.of(instantiations.get(sv));
        } else {
            return Optional.empty();
        }
    }

}
