package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.AbstractContractDefinition;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.util.Pair;

/**
 * The class is used to add Taclets from specification repository to the existing proof.
 * 
 * @author Maria Pelevina
 *
 */

public class TacletToProofLoader {
	private Proof proof;
	private Services services;
	private ProofEnvironment proofEnv;
	private SpecificationRepository specRepos;

	public TacletToProofLoader(Proof proof) {
		this.proof = proof;
		services = proof.getServices();
		proofEnv = proof.env();
		specRepos = services.getSpecificationRepository();
	}
	
		public void collectAxiomsAndDefs() {
			ImmutableSet<NoPosTacletApp> taclets;
			taclets = DefaultImmutableSet.nil();

			// if (po instanceof FunctionalOperationContractPO) {

			for (KeYJavaType type : services.getJavaInfo().getAllKeYJavaTypes()) {
				final ImmutableSet<AbstractContractDefinition> defs = specRepos
						.getAbstractContractDefinitions(type);
				if (defs != null && defs.isEmpty() == false) {
					for (AbstractContractDefinition def : defs) {
						Taclet defTaclet = def.toTaclet(services);
						// TODO only include if choices are applicable
						
						taclets = taclets.add(NoPosTacletApp
								.createNoPosTacletApp(defTaclet));

						proofEnv.registerRule(defTaclet,
								AxiomJustification.INSTANCE);
					}
				}
			}
			
			IObserverFunction o = specRepos.getTargetOfProof(proof);
			KeYJavaType selfKjt = o.getContainerType();

			final ImmutableSet<ClassAxiom> axioms = specRepos
					.getClassAxioms(selfKjt);
			for (ClassAxiom axiom : axioms) {
				final ImmutableSet<Pair<Sort, IObserverFunction>> scc = getSCC(
						axiom, axioms);
				for (Taclet axiomTaclet : axiom.getTaclets(scc, services)) {
					assert axiomTaclet != null : "class axiom returned null taclet: "
							+ axiom.getName();

					// only include if choices are appropriate
					if (choicesApply(axiomTaclet, proofEnv.getInitConfig()
							.getActivatedChoices())) {
						taclets = taclets.add(NoPosTacletApp
								.createNoPosTacletApp(axiomTaclet));
						proofEnv.registerRule(axiomTaclet,
								AxiomJustification.INSTANCE);
					}
				}
			}
			proof.getGoal(proof.root()).indexOfTaclets().addTaclets(taclets);
		}

		private boolean choicesApply(Taclet taclet, ImmutableSet<Choice> choices) {
			for (Choice tacletChoices : taclet.getChoices())
				if (!choices.contains(tacletChoices))
					return false;
			return true;
		}
		
		// really necessary?
		private ImmutableSet<Pair<Sort, IObserverFunction>> getSCC(
				ClassAxiom startAxiom, ImmutableSet<ClassAxiom> axioms) {
			// TODO: make more efficient
			final Pair<Sort, IObserverFunction> start = new Pair<Sort, IObserverFunction>(
					startAxiom.getKJT().getSort(), startAxiom.getTarget());
			ImmutableSet<Pair<Sort, IObserverFunction>> result = DefaultImmutableSet
					.nil();
			for (ClassAxiom nodeAxiom : axioms) {
				final Pair<Sort, IObserverFunction> node = new Pair<Sort, IObserverFunction>(
						nodeAxiom.getKJT().getSort(), nodeAxiom.getTarget());
				if (reach(start, node, axioms) && reach(node, start, axioms)) {
					result = result.add(node);
				}
			}
			return result;
		}

		private boolean reach(Pair<Sort, IObserverFunction> from,
				Pair<Sort, IObserverFunction> to, ImmutableSet<ClassAxiom> axioms) {
			ImmutableSet<Pair<Sort, IObserverFunction>> reached = DefaultImmutableSet
					.nil();
			ImmutableSet<Pair<Sort, IObserverFunction>> newlyReached = DefaultImmutableSet
					.<Pair<Sort, IObserverFunction>> nil().add(from);

			while (!newlyReached.isEmpty()) {
				for (Pair<Sort, IObserverFunction> node : newlyReached) {
					newlyReached = newlyReached.remove(node);
					reached = reached.add(node);
					final ImmutableSet<ClassAxiom> nodeAxioms = getAxiomsForObserver(
							node, axioms);
					for (ClassAxiom nodeAxiom : nodeAxioms) {
						final ImmutableSet<Pair<Sort, IObserverFunction>> nextNodes = nodeAxiom
								.getUsedObservers(services);
						for (Pair<Sort, IObserverFunction> nextNode : nextNodes) {
							if (nextNode.equals(to)) {
								return true;
							} else if (!reached.contains(nextNode)) {
								newlyReached = newlyReached.add(nextNode);
							}
						}
					}
				}
			}

			return false;
		}
		
	    private ImmutableSet<ClassAxiom> getAxiomsForObserver(
	            Pair<Sort, IObserverFunction> usedObs,
	            ImmutableSet<ClassAxiom> axioms) {
	        for (ClassAxiom axiom : axioms) {
	            if (axiom.getTarget()==null || !(axiom.getTarget().equals(usedObs.second)
	                  && usedObs.first.extendsTrans(axiom.getKJT().getSort()))) {
	                axioms = axioms.remove(axiom);
	            }
	        }
	        return axioms;
	    }

}
