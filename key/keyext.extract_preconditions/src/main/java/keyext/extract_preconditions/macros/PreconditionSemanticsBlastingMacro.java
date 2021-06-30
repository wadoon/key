package keyext.extract_preconditions.macros;

import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.Rule;

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

}
