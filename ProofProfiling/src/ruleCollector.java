import java.util.ArrayList;
import java.util.List;

import org.json.JSONException;
import org.json.JSONObject;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

public class ruleCollector {
	public  String getRuleApplied(Node n)  {
		List<String> ruleNameList = new ArrayList<>();
		String ruleName;
			Rule r = n.getAppliedRuleApp().rule();
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					ruleNameList.add(rs.name().toString());
				}
				ruleName = ruleNameList.toString().replace("[", "").replace("]", "");
			}
			else {
				ruleName="null";	
			}
		
		return ruleName;
	}

	
	public  JSONObject getRuleCount(Node n,JSONObject rule ) throws JSONException {	
		if(n.childrenCount()>=1 && !n.leaf()) {
			Rule r = n.getAppliedRuleApp().rule();
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					long count = 1;		
					Object value = rule.has(rs.name().toString()) ?
							rule.get(rs.name().toString()) : null;
							System.out.println(value);
					if (value instanceof Long) {
						count = ((Long)value) + 1;
					} else if (value != null) {
						throw new IllegalStateException();
					}
					
					rule.put(rs.name().toString(), count);
					System.out.println(rule);
				}
				if(n.childrenCount()==1) {
					getRuleCount(n.child(0),rule);
				}
				 
			}
		}
		System.out.println(rule);
		return rule;
	}
}
