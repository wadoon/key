package de.uka.ilkd.key.strategy.termgenerator;

import java.util.Iterator;
import java.util.LinkedHashSet;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.UpdateApplication;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * The heap generator returns an iterator over all terms of sort heap 
 * that 
 * <ol> 
 * <li>can be found in the sequent</li>
 * <li>are top level in the sense that they are not part of a larger term expression</li>
 * <li>depending on the mode: heaps just occurring in updates are included or ignored</li>  
 * </ol>
 */
public class HeapGenerator implements TermGenerator {

    public static final TermGenerator INSTANCE = new HeapGenerator(true);
    public static final TermGenerator INSTANCE_EXCLUDE_UPDATES = new HeapGenerator(false);

    private final boolean includeUpdates;
    
    private HeapGenerator(boolean includeUpdates) {
        this.includeUpdates = includeUpdates;        
    }
    
    @Override
    public Iterator<JavaDLTerm> generate(RuleApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
        LinkedHashSet<JavaDLTerm> heaps = new LinkedHashSet<>();
        Sequent seq = goal.sequent();
        for (SequentFormula<JavaDLTerm> sf : seq) {
            collectHeaps(sf.formula(), heaps, goal.proof().getServices());
        }
        return heaps.iterator();
    }

    private void collectHeaps(JavaDLTerm term, LinkedHashSet<JavaDLTerm> heaps, Services services) {
        if (term.sort().equals(services.getTheories().getHeapLDT().targetSort())) {
            heaps.add(term);
        } else {
            if (!includeUpdates && term.op() instanceof UpdateApplication) {
                collectHeaps(UpdateApplication.getTarget(term), heaps, services);
            } else {
                for (int i = 0; i < term.arity(); i++) {
                    collectHeaps(term.sub(i), heaps, services);
                }
            }
        }
    }

}
