package smt;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class AuxiliaryFunctions {

	public static List<Proof> createProofsForTesting(Proof proof) {
		final List<Node> nodes = new LinkedList<Node>();
		final ImmutableList<Goal> oldGoals = proof.openGoals();
		if (proof.closed()) {
			getNodesWithEmptyModalities(proof.root(), nodes);
		} else {
			for (final Goal goal : oldGoals) {
				nodes.add(goal.node());
			}
		}
		final Iterator<Node> oldGoalIter = nodes.iterator();
		final List<Proof> result = new LinkedList<Proof>();
		while (oldGoalIter.hasNext()) {
			try {
				Proof p = null;
				p = createProofForTesting_noDuplicate(oldGoalIter.next(), result, true);
				if (p != null) {
					result.add(p);
				}
			} catch (final Exception e) {
				System.err.println(e.getMessage());
			}
		}
		return result;
	}

	public static Proof createProofForTesting_noDuplicate(Node node, List<Proof> otherProofs, boolean removePostCondition)
			throws ProofInputException {
		// System.out.println("Create proof for test case from Node:"+node.serialNr());
		final Proof oldProof = node.proof();
		final Sequent oldSequent = node.sequent();
		Sequent newSequent = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT, Semisequent.EMPTY_SEMISEQUENT);
		Iterator<SequentFormula> it = oldSequent.antecedent().iterator();
		while (it.hasNext()) {
			final SequentFormula sf = it.next();
			// Allow updates modailities in the antecedent
			if (hasModalities(sf.formula(), false)) {
				continue;
			}
			newSequent = newSequent.addFormula(sf, true, false).sequent();
		}
		it = oldSequent.succedent().iterator();
		//TODO: Daniel: auskommentieren bringt etwas? vlt. weil man dadurch bei innerLoop die inv entfernt, die
		//den sequent allgemeingültig macht?
		while (it.hasNext()) {
			final SequentFormula sf = it.next();
			if (hasModalities(sf.formula(), removePostCondition)) {
				continue;
			}
			newSequent = newSequent.addFormula(sf, false, false).sequent();
		}
		// Check if a proof with the same sequent already exists.
		if (otherProofs != null) {
			for (final Proof otherProof : otherProofs) {
				if (otherProof.root().sequent().equals(newSequent)) {
					// System.out.println("Found and skip duplicate proof for
					// node:"+node.serialNr());
					return null;
				}
			}
		}
		return createProof(oldProof, "Test Case for NodeNr: " + node.serialNr(), newSequent);
	}
	
	public static boolean hasModalities(Term t, boolean checkUpdates) {
		final JavaBlock jb = t.javaBlock();
		if (jb != null && !jb.isEmpty()) {
			// System.out.println("Excluded javablock");
			return true;
		}
		if (t.op() == UpdateApplication.UPDATE_APPLICATION && checkUpdates) {
			// System.out.println("Exclude update application.");
			return true;
		}
		boolean res = false;
		for (int i = 0; i < t.arity() && !res; i++) {
			res |= hasModalities(t.sub(i), checkUpdates);
		}
		return res;
	}

	public static void getNodesWithEmptyModalities(Node root, List<Node> nodes) {
		if (root.getAppliedRuleApp() != null) {
			final RuleApp app = root.getAppliedRuleApp();
			if (app.rule().name().toString().equals("emptyModality")) {
				nodes.add(root);
			}
		}
		for (int i = 0; i < root.childrenCount(); ++i) {
			getNodesWithEmptyModalities(root.child(i), nodes);
		}
	}

	public static Proof createProof(Proof proof, String proofName, Sequent newSequent) throws ProofInputException {
		Choice choice = new Choice("ban", "runtimeExceptions");
		ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(proof, choice);
		ProofStarter starter = SideProofUtil.createSideProof(env, newSequent, proofName);
		Proof newProof = starter.getProof();
		SpecificationRepository specRepo = newProof.getServices().getSpecificationRepository();
		ProofOblInput proofOblInput = specRepo.getProofOblInput(proof);
		specRepo.registerProof(proofOblInput, newProof);
		OneStepSimplifier.refreshOSS(newProof);
		return newProof;
	}

}
