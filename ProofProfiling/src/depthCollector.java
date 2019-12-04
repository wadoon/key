import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.json.JSONException;
import org.json.JSONObject;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;


public class depthCollector {
	public  JSONObject getNodeDepth(Node n) throws JSONException {
		Iterator<SequentFormula> it = n.sequent().iterator();
		List<Double> doubleDepth = new ArrayList<>();
		JSONObject depthJson = new JSONObject();
		System.out.println(it);
		while(it.hasNext()) {
            SequentFormula cf = it.next();
            doubleDepth.add(Double.valueOf(cf.formula().depth()));
            
        }
		depthJson = countDepth(doubleDepth);
		
		return depthJson;
	}
	
	public  JSONObject countDepth(List<Double> depth) throws JSONException {
		JSONObject depthObject = new JSONObject();
		double total = 0, avgMax = 0;

        for (int counter = 0; counter < depth.size(); counter++)
        {
         total += depth.get(counter);
        }

        avgMax = total / depth.size();
        
        double max = depth.get(0);
        double min = depth.get(0);

        for (int counter = 1; counter < depth.size(); counter++)
        {
         if (depth.get(counter) > max)
         {
          max = depth.get(counter);
         
         }
         if (depth.get(counter) < min)
         {
        	 min = depth.get(counter);
         }
        }   
        depthObject.put("max", max);
        depthObject.put("min", min);
        depthObject.put("avg", avgMax);
        depthObject.put("total", total);
        return depthObject;
	}
}
