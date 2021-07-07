package keyext.extract_preconditions.macros;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.Strategy;

import java.util.HashSet;

/**
 * Based on de.uka.ilkd.key.macros.PreconditionSemanticsBlastingMacro
 */
public final class PreconditionSemanticsBlastingMacro extends SemanticsBlastingMacro {

	private PreconditionSemanticsRuleFilter preconditionSemanticRuleFilter;
	private PreconditionEqualityRuleFilter preconditionEqualityRuleFilter;

	public PreconditionSemanticsBlastingMacro() {
		super();
		allowedPullOut.remove("store");
		preconditionSemanticRuleFilter = new PreconditionSemanticsRuleFilter();
		preconditionEqualityRuleFilter = new PreconditionEqualityRuleFilter();

	}

	@Override
	protected RuleFilter getSemanticsRuleFilter () {
		return preconditionSemanticRuleFilter;
	}

	@Override
	protected RuleFilter getEqualityRuleFilter () {
		return preconditionEqualityRuleFilter;
	}


	@Override
	protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
		return new PreconditionSemanticsBlastingStrategy();
	}

	private class PreconditionSemanticsRuleFilter extends SemanticsRuleFilter {
		protected HashSet<String> allowedRulesNames;

		{
			allowedRulesNames = new HashSet<String>(100);
			allowedRulesNames.add("execEmpty");
			allowedRulesNames.add("emptyModality");
			allowedRulesNames.add("emptyModalityBoxTransaction");
			allowedRulesNames.add("emptyModalityDiamondTransaction");
			allowedRulesNames.add("tryEmpty");
			allowedRulesNames.add("tryFinallyEmpty");
			allowedRulesNames.add("blockEmpty");
			allowedRulesNames.add("methodCallEmpty");
			allowedRulesNames.add("emptyStatement");
			allowedRulesNames.add("hideAuxiliaryEq");
		}

		@Override
		public boolean filter(Rule rule) {
			return allowedRulesNames.contains(rule.name().toString()) || super.filter(rule);
		}
	}

	private class PreconditionEqualityRuleFilter extends EqualityRuleFilter {
		private HashSet<String> allowedRulesNames;
		{
			allowedRulesNames = new HashSet<String>();
			allowedRulesNames.add("minAxiom");
			allowedRulesNames.add("Use Operation Contract");
			allowedRulesNames.add("assignment");
			allowedRulesNames.add("methodCallWithAssignment");
			allowedRulesNames.add("variableDeclaration");
		}

		@Override
		public boolean filter(Rule rule) {
			return allowedRulesNames.contains(rule.name().toString()) || super.filter(rule);
		}
	}


	protected void addInvariantFormula(Goal goal) {
		// DO NOTHING
		return;
	}

	private class PreconditionSemanticsBlastingStrategy extends SemanticsBlastingStrategy {
		public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
			if (app.rule().name().toString().equals("hideAuxiliaryEq")) {
				Term curTerm = pio.subTerm();
				if (this.isAuxiliaryEq(curTerm.sub(0))
					|| this.isAuxiliaryEq(curTerm.sub(1))) {
					return true;
				}
				return false;
			}
			return super.isApprovedApp(app, pio, goal);
		}

		private boolean isAuxiliaryEq(Term t) {
			// True if equality between heaps or
			// True if equality between something and select of something that isn't `heap`
			return t.sort().name().toString().equals("Heap")
					|| (
						t.op().name().toString().endsWith("::select")
						&& (! (t.sub(0).op() instanceof LocationVariable)
							|| !t.sub(0).op().name().toString().equals("heap"))
						);
		}
	}
}
