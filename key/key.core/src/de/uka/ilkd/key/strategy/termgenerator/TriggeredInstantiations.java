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

package de.uka.ilkd.key.strategy.termgenerator;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Metavariable;
import de.uka.ilkd.key.strategy.quantifierHeuristics.PredictCostProver;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;

public class TriggeredInstantiations implements TermGenerator {

    public static TermGenerator create(boolean skipConditions) {
        return new TriggeredInstantiations(skipConditions);
    }
    
    private Sequent last = Sequent.EMPTY_SEQUENT;
    private Set<JavaDLTerm> lastCandidates = new HashSet<JavaDLTerm>();
    private ImmutableSet<JavaDLTerm> lastAxioms = DefaultImmutableSet.<JavaDLTerm>nil();
    
    private boolean checkConditions;

    /**
     * 
     * @param checkConditions boolean indicating if conditions should be checked
     */
    public TriggeredInstantiations(boolean checkConditions) {
        this.checkConditions = checkConditions;
    }
    
    @Override
    /**
     * Generates all instances 
     */
    public Iterator<JavaDLTerm> generate(RuleApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
        if (app instanceof TacletApp) {

            final Services services = goal.proof().getServices();
            final TacletApp tapp = (TacletApp) app;
            final Taclet taclet = tapp.taclet();

            final Set<JavaDLTerm> terms;
            final Set<JavaDLTerm> axiomSet;
            ImmutableSet<JavaDLTerm> axioms = DefaultImmutableSet.<JavaDLTerm>nil();
 
            
            final Sequent seq = goal.sequent();
            if (seq != last) {
                terms = new HashSet<JavaDLTerm>();
                axiomSet = new HashSet<JavaDLTerm>();
                computeAxiomAndCandidateSets(seq, terms, axiomSet, services);
                for (JavaDLTerm axiom : axiomSet) {
                    axioms = axioms.add(axiom);
                }

                synchronized (this) {
                    last = seq;
                    lastCandidates = terms;
                    lastAxioms = axioms;
                }
            } else {
                synchronized (this) {
                    terms = lastCandidates;
                    axioms = lastAxioms;
                }
            }

            if (taclet.hasTrigger()) {

                final JavaDLTerm comprehension = pos.subTerm();

                if (tapp.uninstantiatedVars().size() <= 1) {
                    SVInstantiations svInst = tapp.instantiations();

                    final SchemaVariable sv = taclet.getTrigger()
                            .getTriggerVar();
                    final Sort svSort;
                    if (sv.sort() instanceof GenericSort) {
                        svSort = svInst.getGenericSortInstantiations()
                                .getRealSort(sv, services);
                    } else {
                        svSort = sv.sort();
                    }

                    final Metavariable mv = new Metavariable(new Name("$MV$"
                            + sv.name()), svSort);

                    final JavaDLTerm trigger = instantiateTerm(
                            taclet.getTrigger().getTerm(), services,
                            svInst.replace(sv, services.getTermBuilder().var(mv), services));

                    final Set<JavaDLTerm> instances = computeInstances(services,
                            comprehension, mv, trigger, terms, axioms, tapp);

                    return instances.iterator();
                } else {
                    // at the moment instantiations with more than one
                    // missing taclet variable not supported
                    return ImmutableSLList.<JavaDLTerm> nil().iterator();
                }
            } else {
                return ImmutableSLList.<JavaDLTerm> nil().iterator();
            }

        } else {
            throw new IllegalArgumentException(
                    "At the moment only taclets are supported.");
        }

    }

    private JavaDLTerm instantiateTerm(final JavaDLTerm term, final Services services,
            SVInstantiations svInst) {
        final SyntacticalReplaceVisitor syn = new SyntacticalReplaceVisitor(
              new TermLabelState(), null, null, svInst, null, null, null, services);
        term.execPostOrder(syn);
        return syn.getTerm();
    }

    private void computeAxiomAndCandidateSets(final Sequent seq,
            final Set<JavaDLTerm> terms, final Set<JavaDLTerm> axioms, Services services) {        
        final IntegerLDT integerLDT = services.getTheories().getIntegerLDT();
        collectAxiomsAndCandidateTerms(terms, axioms, integerLDT, seq.antecedent(), true, services);
        collectAxiomsAndCandidateTerms(terms, axioms, integerLDT, seq.succedent(), false, services);
    }

    private void collectAxiomsAndCandidateTerms(final Set<JavaDLTerm> terms,
            final Set<JavaDLTerm> axioms, final IntegerLDT integerLDT,
            Semisequent antecedent, boolean inAntecedent, JavaDLTermServices services) {
        
        for (SequentFormula<JavaDLTerm> sf : antecedent) {
            collectTerms(sf.formula(), terms, integerLDT);
            if (sf.formula().op() instanceof Function || 
                    sf.formula().op() == Equality.EQUALS) {
                axioms.add(inAntecedent ? sf.formula() : services.getTermBuilder().not(sf.formula()));
            }
        }
    }

    private boolean isAvoidConditionProvable(JavaDLTerm cond, ImmutableSet<JavaDLTerm> axioms,
            Services services) {
        
        long cost = PredictCostProver.computerInstanceCost(
                new Substitution(DefaultImmutableMap.<QuantifiableVariable, JavaDLTerm>nilMap()), 
                cond, axioms, services);
        return cost == -1;
    }

    private HashSet<JavaDLTerm> computeInstances(Services services,
            final JavaDLTerm comprehension, final Metavariable mv,
            final JavaDLTerm trigger, Set<JavaDLTerm> terms, ImmutableSet<JavaDLTerm> axioms, TacletApp app) {

        final HashSet<JavaDLTerm> instances = new HashSet<JavaDLTerm>();
        final HashSet<JavaDLTerm> alreadyChecked = new HashSet<JavaDLTerm>();

        for (final JavaDLTerm t : terms) {
            boolean addToInstances = true;
            Constraint c = EqualityConstraint.BOTTOM.unify(trigger, t, services);
            if (c.isSatisfiable()) {
                final JavaDLTerm middle = c.getInstantiation(mv, services);
                if (middle != null && !alreadyChecked.contains(middle)) {
                    alreadyChecked.add(middle);
                    if (!checkConditions && app.taclet().getTrigger().hasAvoidConditions()) {
                        ImmutableList<JavaDLTerm> conditions = instantiateConditions(services, app, middle);
                        for (JavaDLTerm condition : conditions) {
                            if (isAvoidConditionProvable(condition, axioms, services)) {
                                addToInstances = false;
                                break;
                            }
                        }
                    }
                    if (addToInstances) {
                        instances.add(middle);
                    }
                }
            }
        }
        return instances;
    }

    private ImmutableList<JavaDLTerm> instantiateConditions(Services services,
            TacletApp app, final JavaDLTerm middle) {
        ImmutableList<JavaDLTerm> conditions;
        conditions = ImmutableSLList.<JavaDLTerm> nil();
        for (JavaDLTerm singleAvoidCond : app.taclet().getTrigger().getAvoidConditions()) {
            conditions = conditions.append(instantiateTerm(
                    singleAvoidCond,
                    services,                    
                    app.instantiations().replace(
                            app.taclet().getTrigger().getTriggerVar(), middle,
                            services)));
        }
        return conditions;
    }

    private void collectTerms(JavaDLTerm instanceCandidate, Set<JavaDLTerm> terms,
            IntegerLDT intLDT) {
        if (instanceCandidate.freeVars().isEmpty()
                && !instanceCandidate.containsModalContentRecursive()) {
            terms.add(instanceCandidate);
        }
        if (intLDT.getNumberSymbol() != instanceCandidate.op()) {
            for (int i = 0; i < instanceCandidate.arity(); i++) {
                collectTerms(instanceCandidate.sub(i), terms, intLDT);
            }
        }
    }

}