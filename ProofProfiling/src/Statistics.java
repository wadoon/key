
import java.util.ArrayList;
import java.util.List;
import org.json.JSONException;
import org.json.JSONObject;
import de.uka.ilkd.key.proof.Node;


public class Statistics {
	
	
	public  JSONObject getStatistics(Node n) throws JSONException {
		
		 JSONObject parent = new JSONObject();
		 List<Double> doubleNodeDepthList = new ArrayList<>();
		 List<Long> longNodeTimeList = new ArrayList<>();
		 JSONObject rootNodeObject = new JSONObject();
		 
		 ruleCollector ruleCollector = new ruleCollector();
		 depthCollector depthCollector = new depthCollector();
		 timeCollector timeCollector = new timeCollector();
		 rootNodeObject = depthCollector.getNodeDepth(n);
		 
		 parent.put("name", n.name());
		 parent.put("id", n.serialNr());
		 parent.put("rules", ruleCollector.getRuleApplied(n));
		 parent.put("nodeDepth", rootNodeObject);
		 parent.put("nodeTime", timeCollector.getNodeTime(n));
		
		 doubleNodeDepthList.add(rootNodeObject.getDouble("avg"));
		 longNodeTimeList.add(timeCollector.getNodeTime(n));
		 
		 if(n.childrenCount()>=1 && !n.leaf()) {	
				int k=0;
				for(int i=0;i<=k;i++) {
					JSONObject childJson = new JSONObject();
					childJson.put("name", n.child(0).name());
					childJson.put("id",n.child(0).serialNr());
			
					if(!n.child(0).leaf()) {
						childJson.put("rules",ruleCollector.getRuleApplied(n.child(0)));	
						childJson.put("nodeTime",timeCollector.getNodeTime(n.child(0)));
						longNodeTimeList.add(timeCollector.getNodeTime(n.child(0)));
					}
					else
					{
						childJson.put("rules","null");
						childJson.put("nodeTime",0);
					}
					 
					childJson.put("nodeDepth",depthCollector.getNodeDepth(n.child(0)));
					doubleNodeDepthList.add(depthCollector.getNodeDepth(n.child(0)).getDouble("avg"));
					if (n.child(0).childrenCount()==1) {
						k++;
						n=n.child(0);
					}
					parent.accumulate("children",childJson);
					
				}
				parent.put("branchNodeDepths",doubleNodeDepthList);
				parent.put("branchNodeTimes",longNodeTimeList);
				parent.put("branchNodeDepthDetails",depthCollector.countDepth(doubleNodeDepthList));
				parent.put("branchNodeTimeDetails",timeCollector.countTime(longNodeTimeList));
				
		}
		return parent;
	}
	
}
