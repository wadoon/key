package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

public class RuleExtractor {
	
	private static String RULENAME_PREFIX = "strindc_";
	private static String RULENAME_POSTFIX = "";
	
	private Proof proof;
	
	public RuleExtractor(Proof p) {
		proof = p;
	}
	
	/**
	 * 
	 * @return a LinkedList&lt;Rule&gt; with all rules of the proof which are fit the name convention.
	 */
	public LinkedList<Rule> getRules(){
		LinkedList<Rule> rules = new LinkedList<Rule>();
		ImmutableList<Named> rulesFromNamespace = proof.getServices().getNamespaces().ruleSets().elements();
		for(Named n : rulesFromNamespace){
			Rule r = (Rule)n;
			if(checkNameConvention(r)){
				rules.add(r);
			}
		}
		return rules;
	}

	/**
	 * 
	 * @param r a Rule
	 * @return true if the name convention is true, false else.
	 */
	private boolean checkNameConvention(Rule r){
		String rulename = r.name().toString();
		return (rulename.startsWith(RULENAME_PREFIX)) && (rulename.endsWith(RULENAME_POSTFIX));
	}
}
