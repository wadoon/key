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

package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Immutables;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.util.Pair;

/**
 * This class is meant to replace the equality management built into the
 * {@link JavaCardDLStrategy}.
 *
 * @author Mattias Ulbrich
 */
public class ApplyEqualityEngine {

    private static final Name APPLY_EQ = new Name("applyEq");

    /**
     * The table from sequent formulas (and respective sides) to maps from terms
     * to occurrences.
     */
    private final Map<PosInOccurrence, Map<Term, ImmutableList<PosInOccurrence>>> lobalDepthTable =
            new LRUCache<PosInOccurrence, Map<Term, ImmutableList<PosInOccurrence>>>(1000);

    /**
     * The taclet to build the RuleApps with.
     */
    private final NoPosTacletApp applyEqTaclet;

    /**
     * The services.
     */
    private final Services services;

    /**
     * Instantiates a new engine.
     *
     * It can be used for all goals. It keeps a largish cache.
     *
     * @param index
     *            the taclet index from which the applyEq taclet is taken
     * @param services
     *            the services of the proof
     */
    public ApplyEqualityEngine(TacletIndex index, Services services) {
        this.services = services;
        this.applyEqTaclet = index.lookup(APPLY_EQ);
    }

    /**
     * The central method.
     *
     * It analyzes the goal for application of equality. And if a rule cheaper
     * than cost is found it is re turned, otherwise the originalApp is
     * returned.
     *
     * @param g
     *            the non-null goal
     * @param cost
     *            the (possibly null?) cost of the original app.
     * @param originalAp
     *            the original app against which the equality is cheked
     * @return the chosen rule app
     */
    private final static boolean ACTIVE = true;
    public RuleApp consider(Goal g, RuleAppCost cost, RuleApp originalApp) {

        if(!ACTIVE) {
            return originalApp;
        }

        List<TacletApp> tacletApps = collectRuleApps(g);

        Pair<RuleApp, RuleAppCost> pair = computeCheapestApp(g, tacletApps);

        if(pair == null || cost == null) {
            return originalApp;
        }

        if(pair.second.compareTo(cost) > 0) {
            return originalApp;
        }

        return pair.first;
    }

    /**
     * Compute cheapest app from a list of apps.
     *
     * @param g
     *            the goal for cost computation
     * @param tacletApps
     *            the taclet apps
     * @return the pair of rule app and its costs, <code>null</code> if there is
     *         no app at all
     */
    private Pair<RuleApp, RuleAppCost> computeCheapestApp(Goal g, List<TacletApp> tacletApps) {
        TacletApp best = null;
        RuleAppCost min = TopRuleAppCost.INSTANCE;
        for (TacletApp app : tacletApps) {
            PosInOccurrence pio = app.posInOccurrence();
            RuleAppCost costs = computeCosts(g, app, pio);
            if(costs.compareTo(min) < 0) {
                min = costs;
                best = app;
            }
        }

        if(best != null) {
            return new Pair<RuleApp, RuleAppCost>(best, min);
        } else {
            return null;
        }
    }

    /**
     * Collect all rule app with equalities.
     *
     * @param g
     *            the goal open which to operate
     * @return a freshly created list
     */
    private List<TacletApp> collectRuleApps(Goal g) {
        Sequent seq = g.sequent();
        List<TacletApp> result = new ArrayList<TacletApp>();

        // iterate over all equalities in the antecedent
        int no = 1;
        for (SequentFormula sf : seq.antecedent()) {
            Term formula = sf.formula();
            if(formula.op() == Equality.EQUALS) {
                Term lhs = formula.sub(0);
                PosInOccurrence lhsPIO =
                        new PosInOccurrence(sf, PosInTerm.getTopLevel().down(0), true);

                // now iterate over all formulas in the sequent.
                int i = 0;
                for (SequentFormula tocheck : seq) {
                    i++;

                    if(tocheck == sf) {
                        continue;
                    }
                    // And find the lhs of the equation in there (via caches)
                    ImmutableList<PosInOccurrence> hits = findOccurrences(lhs,
                            new PosInOccurrence(tocheck, PosInTerm.getTopLevel(),
                                    seq.numberInAntec(i)));
                    for (PosInOccurrence hit : hits) {
                        // and add rule applications
                        if(!hit.equals(lhsPIO)) {
                            addEqRuleApplication(g, result, hit, no);
                        }
                    }
                }
            }
            no++;
        }

        return result;
    }

    /**
     * Generate a rule app and add it to a collection.
     *
     * @param g
     *            the goal to operate on
     * @param result
     *            the list of apps to add to
     * @param hit
     *            the {@link PosInOccurrence} of the find clause
     * @param number
     *            the number of the equality as index into the sequent.
     */
    private void addEqRuleApplication(Goal g, List<TacletApp> result,
            PosInOccurrence hit, int number) {

        Sequent sequent = g.sequent();
        Services services = g.proof().getServices();

        NoPosTacletApp app = applyEqTaclet;

        app = app.matchFind(hit, services);
        TacletApp app2 = app.setPosInOccurrence(hit, services);

        IfFormulaInstSeq ifInst = new IfFormulaInstSeq(sequent, number);
        ImmutableList<IfFormulaInstantiation> assumes =
                Immutables.<IfFormulaInstantiation>singletonList(ifInst);

        app2 = app2.setIfFormulaInstantiations(assumes, services);

        if(app2 == null) {
//            throw new Error("Debug: This should not happen ...");
        } else {
            result.add(app2);
        }
    }

    /**
     * Find occurrences of a term in a sequent formula.
     *
     * @param lhs
     *            the term to search
     * @param pio
     *            the pio of the sequent formula to search
     * @return an immutable list of found hits, not <code>null</code>
     */
    private ImmutableList<PosInOccurrence> findOccurrences(Term lhs, PosInOccurrence pio) {

        Map<Term, ImmutableList<PosInOccurrence>> table = getTable(pio);

        ImmutableList<PosInOccurrence> result = table.get(lhs);
        if(result == null) {
            return ImmutableSLList.nil();
        }
        return result;
    }

    /**
     * Gets the lookup table for a {@link PosInOccurrence}.
     *
     * Looks into cache first, creates if not present.
     *
     * @param pio
     *            the index of the sequent formula to look for
     * @return the lookup table, not <code>null</code>
     */
    private Map<Term, ImmutableList<PosInOccurrence>> getTable(PosInOccurrence pio) {

        Map<Term, ImmutableList<PosInOccurrence>> result = lobalDepthTable.get(pio);
        if(result != null) {
            return result;
        }

        result = new HashMap<>();

        sinkInto(result, pio.sequentFormula().formula(), pio);

        lobalDepthTable.put(pio, result);

        return result;
    }

    /*
     * recursively add subterm occurrences into a map.
     */
    private void sinkInto(Map<Term, ImmutableList<PosInOccurrence>> result,
            Term term, PosInOccurrence pio) {

        ImmutableList<PosInOccurrence> list = result.get(term);
        if(list == null) {
            list = ImmutableSLList.<PosInOccurrence>nil();
        }
        list = list.prepend(pio);
        result.put(term, list);

        if(term.op() instanceof Modality || term.op() == UpdateApplication.UPDATE_APPLICATION) {
            // do not try to apply equality inside update / modality.
            return;
        }

        ImmutableArray<Term> subs = term.subs();
        for (int i = 0; i < subs.size(); i++) {
            sinkInto(result, subs.get(i), pio.down(i));
        }

    }

    /**
     * Compute costs.
     *
     * @param goal the goal
     * @param ra the ra
     * @param pos the pos
     * @return the rule app cost
     */
    private RuleAppCost computeCosts(Goal goal, RuleApp ra, PosInOccurrence pos) {
        return goal.getGoalStrategy().computeCost(ra, pos, goal);
    }

}
