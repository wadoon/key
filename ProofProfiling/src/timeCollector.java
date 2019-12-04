import java.util.List;
import org.json.JSONException;
import org.json.JSONObject;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;


public class timeCollector {
	
	public  long getNodeTime(Node n) {
		return n.child(0).getCreationTime()-n.getCreationTime();
	}
	
	public  JSONObject countTime(List<Long> time) throws JSONException {
		JSONObject timeObject = new JSONObject();
		long total = 0, avgMax = 0;

        for (int counter = 0; counter < time.size(); counter++)
        {
         total += time.get(counter);
        }

        avgMax = total / time.size();
        
        long max = time.get(0);
        long min = time.get(0);

        for (int counter = 1; counter < time.size(); counter++)
        {
         if (time.get(counter) > max)
         {
          max = time.get(counter);
         
         }
         if (time.get(counter) < min)
         {
        	 min = time.get(counter);
         }
        }   
        timeObject.put("max", max);
        timeObject.put("min", min);
        timeObject.put("avg", avgMax);
        timeObject.put("total", total);
        return timeObject;
	}
	
	public  JSONObject getRuleTime(Node n,JSONObject time ) throws JSONException {
		if(n.childrenCount()>=1 && !n.leaf()) {
			Rule r = n.getAppliedRuleApp().rule();
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					long count = n.getRuleApplicationTime();
					Object value = time.has(rs.name().toString()) ?
							time.get(rs.name().toString()) : null;
							System.out.println(value);
					if (value instanceof Long) {
						count = ((Long)value) + n.getRuleApplicationTime();
					} else if (value != null) {
						throw new IllegalStateException();
					}
					
					time.put(rs.name().toString(), count);
				}
				if(n.childrenCount()==1) {
					getRuleTime(n.child(0),time);
				}
				 
			}
		}
		return time;
	}
}
