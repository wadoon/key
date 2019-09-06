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

import org.key_project.util.collection.DefaultImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;


public class HeuristicInstantiation implements TermGenerator {

    public final static TermGenerator INSTANCE = new HeuristicInstantiation ();

    private HeuristicInstantiation() {}

    @Override
    public Iterator<Term> generate(RuleApp app,
            PosInOccurrence pos,
            Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
        System.out.println("Calling HEUR generate");
        final Term qf = pos.sequentFormula ().formula ();
        final Sequent seq = goal.sequent();
        final Services services = goal.proof().getServices();
        final QuantifiableVariable var =
                qf.varsBoundHere ( 0 ).last ();
        //final LinkedHashSet<Term> cbi = ConflictBasedInstantiation.create(qf, seq, services).getInstantiation();
        //        if(!cbi.isEmpty()) {
        //            System.out.println("Ignoring E-Matching in favor of CBI");
        //            return new HIIterator(cbi.iterator(), var, services);
        //        }
        //        System.out.println("CBI found nothing, try E-Matching");
        final Instantiation ia = Instantiation.create ( qf, goal.sequent(),
                goal.proof().getServices() );
        HIIterator hiit = new HIIterator ( ia.getSubstitution ().iterator (), var, goal.proof().getServices() );
        return hiit;
    }

    private HIIterator empty(QuantifiableVariable var, Services services) {
        return new HIIterator(DefaultImmutableSet.<Term>nil().iterator(), var, services);
    }


    private class HIIterator implements Iterator<Term> {
        private final Iterator<Term>       instances;

        private final QuantifiableVariable quantifiedVar;

        private final Sort                 quantifiedVarSort;
        private final Function             quantifiedVarSortCast;

        private Term                       nextInst = null;
        private final TermServices services;

        private HIIterator(Iterator<Term> it,
                QuantifiableVariable var,
                TermServices services) {
            this.instances = it;
            this.quantifiedVar = var;
            this.services = services;
            quantifiedVarSort = quantifiedVar.sort ();
            quantifiedVarSortCast = quantifiedVarSort.getCastSymbol (services);
            findNextInst ();
        }

        private void findNextInst() {
            while ( nextInst == null && instances.hasNext () ) {
                nextInst = instances.next ();
                if ( !nextInst.sort ().extendsTrans ( quantifiedVarSort ) ) {
                    if ( !quantifiedVarSort.extendsTrans ( nextInst.sort () ) ) {
                        nextInst = null;
                        continue;
                    }
                    nextInst = services.getTermBuilder().func ( quantifiedVarSortCast, nextInst );
                }
            }
        }

        @Override
        public boolean hasNext() {
            return nextInst != null;
        }

        @Override
        public Term next() {
            final Term res = nextInst;
            nextInst = null;
            findNextInst ();
            return res;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}