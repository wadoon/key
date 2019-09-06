package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * A conflict based instantiation generator for quantified terms.\
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 * TODO just kept for development purposes. Remove later.
 */
public class CBITermGenerator implements TermGenerator {

    /** This CBITermGenerators singleton instance */
    private static CBITermGenerator instance;

    /** The private constructor to avoid creation by others */
    private CBITermGenerator() {}

    /**
     * Returns the singleton instance of this TermGenerator. Creates one if none exists.
     *
     * @return The CBITermGenerators singleton instance
     */
    public static CBITermGenerator getInstance() {
        if (CBITermGenerator.instance == null) {
            CBITermGenerator.instance = new CBITermGenerator();
        }
        return CBITermGenerator.instance;
    }

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        final Term formula = pos.sequentFormula().formula();
        final Sequent sequent = goal.sequent();
        final Services services = goal.proof().getServices();
        //final ConflictBasedInstantiation cbi = ConflictBasedInstantiation.create(formula, sequent, pos, services);
        System.out.print("CBI: ");
        // cbi.getInstantiation().forEach(term -> System.out.println(term.toString() + " "));
        System.out.println();
        return null;
    }

}