package de.uka.ilkd.key.strategy;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.FormulaTagManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IfMatchResult;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.IfInstantiationCachePool.IfInstantiationCache;
import de.uka.ilkd.key.util.Debug;

/**
 * This class implements custom instantiation of if-formulas.
 */
public class IfInstantiator {
    private final Goal goal;
    private final Services services;
    private final IfInstantiationCache ifInstCache;

    private ImmutableList<IfFormulaInstantiation> allAntecFormulas;
    private ImmutableList<IfFormulaInstantiation> allSuccFormulas;

    private final TacletAppContainer tacletAppContainer;
    private final Taclet taclet;

    IfInstantiator(TacletAppContainer tacletAppContainer, final Goal goal) {
        this.goal = goal;
        this.services = goal.proof().getServices();
        this.tacletAppContainer = tacletAppContainer;
        this.taclet = tacletAppContainer.getTacletApp().taclet();
        this.ifInstCache = services.getCaches().getIfInstantiationCache().getCache(goal.node());
    }
    
    /**
     * Find all possible instantiations of the if sequent formulas within the
     * sequent "p_seq".
     * @return 
     */
    public ImmutableList<NoPosTacletApp> findIfFormulaInstantiations() {        
        Debug.assertTrue(tacletAppContainer.getTacletApp().ifFormulaInstantiations() == null,
                "The if formulas have already been instantiated");

        final Sequent ifSequent = taclet.ifSequent();
        if (ifSequent.isEmpty()) {
            return ImmutableSLList.<NoPosTacletApp>nil().prepend(tacletAppContainer.getTacletApp());
        } else {
            return findIfFormulaInstantiationsHelp(
                    ifSequent.succedent().asList(), //// Matching with the last formula
                    ifSequent.antecedent().asList(),
                    ImmutableSLList.nil(), 
                    tacletAppContainer.getTacletApp().matchConditions(),
                    false,
                    ImmutableSLList.<NoPosTacletApp>nil());
        }
    }

    /**
     * @param p_all
     *            if true then return all formulas of the particular
     *            semisequent, otherwise only the formulas returned by
     *            <code>selectNewFormulas</code>
     * @return a list of potential if-formula instantiations (analogously to
     *         <code>IfFormulaInstSeq.createList</code>)
     */
    private ImmutableList<IfFormulaInstantiation> getSequentFormulas(boolean p_antec, boolean p_all) {
        if (p_all) {
            return getAllSequentFormulas(p_antec);
        } 

        ImmutableList<IfFormulaInstantiation> cache = getNewSequentFormulasFromCache(p_antec);
        if (cache != null) {
            return cache;
        }

        cache = selectNewFormulas(p_antec);

        addNewSequentFormulasToCache(cache, p_antec);

        return cache;
    }

    /**
     * @return a list of potential if-formula instantiations (analogously to
     *         <code>IfFormulaInstSeq.createList</code>), but consisting only of
     *         those formulas of the current goal for which the method
     *         <code>isNewFormula</code> returns <code>true</code>
     */
    private ImmutableList<IfFormulaInstantiation> selectNewFormulas(boolean p_antec) {
        ImmutableList<IfFormulaInstantiation> res = ImmutableSLList.nil();

        for (final IfFormulaInstantiation ifInstantiation : getAllSequentFormulas(p_antec) ) {
            if (isNewFormulaDirect((IfFormulaInstSeq) ifInstantiation)) {
                res = res.prepend(ifInstantiation);
            }
        }

        return res;
    }

    /**
     * @return true iff the formula described by the argument has been modified
     *         (or introduced) since the latest point of time when the
     *         if-formulas of the enclosing taclet app (container) have been
     *         matched
     */
    private boolean isNewFormula(IfFormulaInstantiation p_ifInstantiation) {
        final IfFormulaInstSeq ifInst = (IfFormulaInstSeq)p_ifInstantiation;
        final ImmutableList<IfFormulaInstantiation> cache = 
                getNewSequentFormulasFromCache(ifInst.inAntec());

        if (cache != null) {
            return cache.contains(ifInst);
        } else {
            return isNewFormulaDirect(ifInst);
        }
    }

    /**
     * @return true iff the formula described by the argument has been modified
     *         (or introduced) since the latest point of time when the
     *         if-formulas of the enclosing taclet app (container) have been
     *         matched (this method does not use the cache)
     */
    private boolean isNewFormulaDirect(IfFormulaInstSeq p_ifInstantiation) {
        final boolean antec = p_ifInstantiation.inAntec();

        final SequentFormula cfma = p_ifInstantiation.getConstrainedFormula();
        final PosInOccurrence pio = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), antec);

        final FormulaTagManager tagManager = goal.getFormulaTagManager();

        final FormulaTag tag = tagManager.getTagForPos(pio);
        final long formulaAge = tagManager.getAgeForTag(tag);

        // The strict relation can be used, because when applying a rule the
        // age of a goal is increased before the actual modification of the
        // goal take place
        return tacletAppContainer.getAge() < formulaAge;
    }

    private ImmutableList<IfFormulaInstantiation> getNewSequentFormulasFromCache(boolean p_antec) {
        return ifInstCache.get(p_antec, tacletAppContainer.getAge());
    }

    private void addNewSequentFormulasToCache(ImmutableList<IfFormulaInstantiation> p_list, boolean p_antec) {
        ifInstCache.put(p_antec, tacletAppContainer.getAge(), p_list);        
    }


    private ImmutableList<IfFormulaInstantiation> getAllSequentFormulas(boolean p_antec) {
        if (allAntecFormulas == null || allSuccFormulas == null) { 
            final Sequent p_seq = goal.sequent();
            allAntecFormulas = IfFormulaInstSeq.createList(p_seq, true, services);
            allSuccFormulas  = IfFormulaInstSeq.createList(p_seq, false, services);
        }

        return p_antec ? allAntecFormulas : allSuccFormulas;
    }

    /**
     * Recursive function for matching the remaining tail of an if sequent
     *
     * @param p_assumesSeqTail
     *            tail of the current semisequent as list
     * @param p_assumesSeqTail2nd
     *            the following semisequent (i.e. antecedent) or null
     * @param p_matchCond
     *            match conditions until now, i.e. after matching the first
     *            formulas of the if sequent
     * @param p_alreadyMatchedNewFor
     *            at least one new formula has already been matched, i.e. a
     *            formula that has been modified recently
     */
    private ImmutableList<NoPosTacletApp> findIfFormulaInstantiationsHelp(ImmutableList<SequentFormula> p_assumesSeqTail,
            ImmutableList<SequentFormula> p_assumesSeqTail2nd, ImmutableList<IfFormulaInstantiation> p_alreadyMatched,
            MatchConditions p_matchCond, boolean p_alreadyMatchedNewFor, ImmutableList<NoPosTacletApp> result) {

        while (p_assumesSeqTail.isEmpty()) {
            if (p_assumesSeqTail2nd == null) {
                // All formulas have been matched, collect the results
                final NoPosTacletApp matchResult = setAllInstantiations(p_matchCond, p_alreadyMatched);
                return matchResult == null ? result : result.prepend(matchResult);
            } else {
                // Change from succedent to antecedent
                p_assumesSeqTail = p_assumesSeqTail2nd;
                p_assumesSeqTail2nd = null;
            }
        }

        // Match the current formula
        final boolean antec = p_assumesSeqTail2nd == null;
        final boolean lastIfFormula = p_assumesSeqTail.size() == 1 && (p_assumesSeqTail2nd == null || p_assumesSeqTail2nd.isEmpty());
        final ImmutableList<IfFormulaInstantiation> formulas = 
                getSequentFormulas(antec, !lastIfFormula || p_alreadyMatchedNewFor);
        
        final IfMatchResult mr = taclet.getMatcher().
                matchIf(formulas, p_assumesSeqTail.head().formula(), p_matchCond, services);
        
        p_assumesSeqTail = p_assumesSeqTail.tail();

        // For each matching formula call the method again to match
        // the remaining terms
        ImmutableList<IfFormulaInstantiation> matchedAssumesFormulaInstantiations = mr.getFormulas();
        ImmutableList<MatchConditions> matchConditionsForInstantiations = mr.getMatchConditions();
        
        final boolean lastAssumesOrAlreadyMatchedNewFor = (lastIfFormula || p_alreadyMatchedNewFor);
        
        while (!matchedAssumesFormulaInstantiations.isEmpty()) {
            final IfFormulaInstantiation ifInstantiation = matchedAssumesFormulaInstantiations.head();
            final MatchConditions matchConditions = matchConditionsForInstantiations.head();
                        
            final boolean nextAlreadyMatchedNewFor = lastAssumesOrAlreadyMatchedNewFor || 
                    isNewFormula((IfFormulaInstSeq) ifInstantiation);
            
            result = findIfFormulaInstantiationsHelp(p_assumesSeqTail, p_assumesSeqTail2nd, p_alreadyMatched.prepend(ifInstantiation),
                    matchConditions, nextAlreadyMatchedNewFor, result);
            
            matchedAssumesFormulaInstantiations = matchedAssumesFormulaInstantiations.tail();
            matchConditionsForInstantiations    = matchConditionsForInstantiations.tail();
        }
        return result; 
    }

    private NoPosTacletApp setAllInstantiations(MatchConditions p_matchCond,
            ImmutableList<IfFormulaInstantiation> p_alreadyMatched) {
        return NoPosTacletApp.createNoPosTacletApp(taclet, 
                p_matchCond.getInstantiations(), p_alreadyMatched, services);
    }
}