package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * A conflict based instantiation generator for quantified terms.\
 *
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class CBITermGenerator implements TermGenerator {

    /*
     * Singleton behavior
     */

    // This objects singleton instance
    private static CBITermGenerator instance;

    // Prevent creation by other classes
    private CBITermGenerator() {}

    /**
     * Returns the instance of this {@link CBITermGenerator} in a
     * singleton-way.
     * <p>
     * Returns an instance of {@link CBITermGenerator} if one has been
     * created. Otherwise a new instance will be created and returned.
     *
     * @return The instance of this {@link CBITermGenerator}
     */
    public static CBITermGenerator getInstance() {
        if (CBITermGenerator.instance == null) {
            CBITermGenerator.instance = new CBITermGenerator();
        }
        return CBITermGenerator.instance;
    }

    /*
     * TermGenerator behavior
     */

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final Term quantifiedFormula = pos.sequentFormula().formula();
        System.out.println("Formula: " + quantifiedFormula.toString());
        StringBuilder sb = new StringBuilder();
        pos.sequentFormula().formula().subs().forEach(e -> sb.append(e.toString() + " "));
        System.out.println("Subs: " + sb.toString());
        System.out.println("Sequent: " + goal.sequent().toString());
        System.out.println("Vars: " + quantifiedFormula.boundVars());
        final CBInstantiation cbInst = CBInstantiation.create(quantifiedFormula, goal.sequent(), goal.proof().getServices());
        System.out.println("CBInst: " + cbInst.toString());
        final QuantifiableVariable var = quantifiedFormula.varsBoundHere(0).last();
        System.out.println("QVar: " + var.toString());
        System.out.println("Sequent: " + pos.sequentFormula().toString());
        System.out.println("Rule: " + app.rule());
        return new CBIIterator(cbInst.getSubstitution().iterator(), var, goal.proof().getServices());
    }

}