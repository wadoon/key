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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.common.core.logic.op.Junctor;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.Quantifier;

/**
 * This class describes the relation between different clauses in a CNF.
 * If two clauses have the same existential quantifiable variable, we say
 * they are connected. And this property is transitive.
 */
public class ClausesGraph {
    private final ImmutableSet<QuantifiableVariable> exVars;
    
    /**
     * Map from <code>JavaDLTerm</code> to <code>ImmutableSet<JavaDLTerm></code>
     */
    private final Map<JavaDLTerm, ImmutableSet<JavaDLTerm>> connections = new LinkedHashMap<JavaDLTerm, ImmutableSet<JavaDLTerm>>();
    
    private final ImmutableSet<JavaDLTerm> clauses;
    
    static ClausesGraph create(JavaDLTerm quantifiedFormula, ServiceCaches caches) {
        final Map<JavaDLTerm, ClausesGraph> graphCache = caches.getGraphCache();
        ClausesGraph graph;
        synchronized (graphCache) {
            graph = graphCache.get ( quantifiedFormula );            
        }
        if ( graph == null ) {
            graph = new ClausesGraph ( quantifiedFormula );
            synchronized (graphCache) {
                graphCache.put ( quantifiedFormula, graph );
            }
        }
        return graph;
    }

    private ClausesGraph(JavaDLTerm quantifiedFormula) {
        exVars = existentialVars ( quantifiedFormula );
        clauses = computeClauses ( TriggerUtils.discardQuantifiers ( quantifiedFormula ) );
        buildInitialGraph ();
        buildFixedPoint ();
    }

    private void buildFixedPoint() {
        boolean changed;
        do {
            changed = false;

            for (JavaDLTerm clause : clauses) {
                final JavaDLTerm formula = clause;
                final ImmutableSet<JavaDLTerm> oldConnections = getConnections(formula);
                final ImmutableSet<JavaDLTerm> newConnections =
                        getTransitiveConnections(oldConnections);

                if (newConnections.size() > oldConnections.size()) {
                    changed = true;
                    connections.put(formula, newConnections);
                }
            }

        } while ( changed );
    }

    private ImmutableSet<JavaDLTerm> getTransitiveConnections(ImmutableSet<JavaDLTerm> formulas) {
        for (JavaDLTerm formula : formulas) formulas = formulas.union(getConnections(formula));
        return formulas;
    }

    /**
     * 
     * @param formula0
     * @param formula1
     * @return ture if clause of formula0 and clause of formula1 
     *         are connected.
     */
    boolean connected(JavaDLTerm formula0, JavaDLTerm formula1) {
        final ImmutableSet<JavaDLTerm> subFormulas1 = computeClauses ( formula1 );
        for (JavaDLTerm term : computeClauses(formula0)) {
            if (intersect(getConnections(term),
                    subFormulas1).size() > 0)
                return true;
        }
        return false;
    }
    
    boolean isFullGraph() {
        final Iterator<JavaDLTerm> it = clauses.iterator ();
        if ( it.hasNext () ) {
            if ( getConnections ( it.next () ).size () < clauses.size () )
                return false;
        }
        return true;
    }
 
 
    /**
     * @param formula
     * @return set of terms that connect to the formula.
     */
    private ImmutableSet<JavaDLTerm> getConnections(JavaDLTerm formula) {
        return connections.get ( formula );
    }

    /**
     * initiate connection map.
     * 
     */
    private void buildInitialGraph() {
        for (JavaDLTerm clause1 : clauses) {
            final JavaDLTerm clause = clause1;
            connections.put(clause, directConnections(clause));
        }
    }

    /**
     * 
     * @param formula
     * @return set of term that connect to formula.
     */
    private ImmutableSet<JavaDLTerm> directConnections(JavaDLTerm formula) {
        ImmutableSet<JavaDLTerm> res = DefaultImmutableSet.<JavaDLTerm>nil();
        for (JavaDLTerm clause1 : clauses) {
            final JavaDLTerm clause = clause1;
            if (directlyConnected(clause, formula))
                res = res.add(clause);
        }
        return res;
    }

    /**
     * 
     * @param set
     * @return ture if set contains one or more exists varaible that are also in
     *         exVars
     */
    private boolean containsExistentialVariables(ImmutableSet<QuantifiableVariable> set) {
        return intersectQV ( set, exVars ).size () > 0;
    }

    /**
     * @param formula0
     * @param formula1
     * @return true if formula0 and formula1 have one or more exists varaible
     *         that are the same.
     */
    private boolean directlyConnected(JavaDLTerm formula0, JavaDLTerm formula1) {
        return containsExistentialVariables ( intersectQV ( formula0.freeVars (),
                                                            formula1.freeVars () ) );
    }

    /**
     * @param formula
     * @return retrun set of terms of all clauses under the formula
     */

    private ImmutableSet<JavaDLTerm> computeClauses(JavaDLTerm formula) {
        final Operator op = formula.op ();
        if ( op == Junctor.NOT )
            return computeClauses ( formula.sub ( 0 ) );
        else if ( op == Junctor.AND ) {
            return computeClauses ( formula.sub ( 0 ) )
                   .union ( computeClauses ( formula.sub ( 1 ) ) );
        } else {
            return DefaultImmutableSet.<JavaDLTerm>nil().add ( formula );
        }
    }

    /**
     * return the exists variables bound in the top level of 
     * a given cnf formula. 
     */
    private ImmutableSet<QuantifiableVariable> existentialVars(JavaDLTerm formula) {
        final Operator op = formula.op ();
        if ( op == Quantifier.ALL ) return existentialVars ( formula.sub ( 0 ) );
        if ( op == Quantifier.EX )
            return
                existentialVars ( formula.sub ( 0 ) )
                .add ( formula.varsBoundHere ( 0 ).last () );
        return DefaultImmutableSet.<QuantifiableVariable>nil();
    }

    /**
     * @return a set of quantifiableVariable which are belonged to 
     *          both set0 and set1 have
     */
    private ImmutableSet<QuantifiableVariable> intersectQV(ImmutableSet<QuantifiableVariable> set0,
                                                ImmutableSet<QuantifiableVariable> set1) {
        return TriggerUtils.intersect ( set0, set1 );
    }
    
    
    /**
     * 
     * @param set0
     * @param set1
     * @return a set of terms which are belonged to both set0 and set1.
     */
    private ImmutableSet<JavaDLTerm> intersect(ImmutableSet<JavaDLTerm> set0, ImmutableSet<JavaDLTerm> set1) {
        ImmutableSet<JavaDLTerm> res = DefaultImmutableSet.<JavaDLTerm>nil();
        if ( set0 == null || set1 == null ) return res;
        for (JavaDLTerm aSet0 : set0) {
            final JavaDLTerm el = aSet0;
            if (set1.contains(el)) res = res.add(el);
        }
        return res;
    }
   
}
