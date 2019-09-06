package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * A term generator that uses
 * @author Andre Challier <andre.challier@stud.tu-darmstadt.de>
 *
 */
public class CbiTermGenerator implements TermGenerator {

    @Override
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos,
            Goal goal) {
        LinkedHashSet<Term> terms = new LinkedHashSet<Term>();
        // TODO insert next instance
        return terms.iterator();
    }

}
