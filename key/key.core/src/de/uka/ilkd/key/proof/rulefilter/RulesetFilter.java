package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

public class RulesetFilter extends TacletFilter {

	private final Name ruleset;
	
	public RulesetFilter(Name ruleset) {
		this.ruleset = ruleset;
	}
	
	@Override
	protected boolean filter(Taclet taclet) {
		for ( RuleSet rs : taclet.getRuleSets() ) {
			if (ruleset.equals(rs.name())) {
				return true;
			}
		}
		return false;
	}

}
