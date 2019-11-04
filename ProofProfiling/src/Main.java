import java.io.BufferedWriter;
import java.util.concurrent.TimeUnit;


import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import io.ProofLoader;
import profiling.Profiler;
import profiling.ProfilingData;
import profiling.statistics.StatisticsProfiler;
import com.google.gson.*;
public class Main {

	final static String PATH = "C:\\Users\\shiva\\git\\key\\key\\key.ui\\examples\\standard_key\\prop_log\\proof\\Iterator(Iterator__next()).proof";
	public static List<Node> parentName = new ArrayList<>();
	public static String ruleName;
	public static Node ruleNode;
	public static Node currentNode;
	public static int ruleNodeSize=0;
	public static int ruleCount=0;
	public static int nodeNumber=0;
	public static int endnode=0;
	public static int nodeNum=0;
	public static int branchNum=0;
	public static float maxBranchDepth=0;
	public static float minBranchDepth=0;
	public static List<Double> treeDepthList = new ArrayList<>();
	public static List<Double> treeTimeList = new ArrayList<>();
	public static JSONArray jsonDepth = new JSONArray();
	
	
	public static JSONObject toJSON(Node n) throws JSONException {
		if(n.childrenCount()==0) {
			JSONObject childJson = new JSONObject();
			childJson.put("name", n.name());
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			JSONObject childJson = new JSONObject();
	
			parentJson.put("name", n.name());
			if (n.childrenCount() > 0) {
				childJson.put("name", new JSONArray());
			}
			
			
			for(int i=0;i<n.childrenCount();i++) {
				childJson.accumulate("name", getNode(n.child(i)).name());	
			}
			
			parentJson.put("children",childJson);
			
			return parentJson;
		}	
	}
	public static JSONObject test(Node n) throws JSONException {

		if(n.childrenCount()==0) {
			JSONObject childJson = new JSONObject();
			childJson.put("name", n.name());
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			
			
			parentJson.put("name", n.name());
			
			if (n.childrenCount() ==1) {
				int k=1;
				for(int i=0;i<k;i++) {
					JSONObject childJson = new JSONObject();
					childJson.put("name", n.child(0).name());
					if (n.child(0).childrenCount()==1) {
						k++;
						n=n.child(0);
						parentJson.accumulate("children",childJson);
					}
					
				}
				
			}
//			System.out.println(parentJson);
			
			return parentJson;
		}	
	}
	
	public static Node getNode(Node n) throws JSONException {
		if(n.child(0).childrenCount() == 1) {
			return n.child(0);
		}
		else {
			toJSON(n);
			return n;
			
		}
	}
	
//	public static JSONObject fullTreeToJson(Node n) throws JSONException {
//		if(n.childrenCount()==0) {
//			JSONObject childJson = new JSONObject();
//			childJson.put("name", n.name());
//			return childJson;
//		}
//		else {
//			JSONObject parentJson = new JSONObject();
//			parentJson.put("name", n.name());
//			if (n.childrenCount() > 1) {
//				parentJson.put("children", new JSONArray());
//				for(int i=0;i<n.childrenCount();i++) {
//					parentJson.accumulate("children", fullTreeToJson(n.child(i)));	
//				}
//			}
//			if (n.childrenCount() == 1) {
//				parentJson.put("children", new JSONArray());
//					accumulateNode( n.child(0),parentJson);
//			}
//			return parentJson;
//		}	
//	}
//	
//	public static JSONObject accumulateNode(Node n,JSONObject parentJson ) throws JSONException {
//		
//		if (n.childrenCount() == 1) {
//			parentJson.accumulate("children", n.name());
//			accumulateNode();
//		}
//	}
//public static List<String> parentName = new ArrayList<>();
	
	
	
	public static JSONObject treeBasedOnNodeName(Node n) throws JSONException {
	
		if(n.childrenCount()==0) {
			JSONObject childJson = new JSONObject();
			childJson.put("size",5);
			childJson.put("name",nodeNum++);
			childJson.put("displayName", n.name());
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			JSONObject ruleStatistics = new JSONObject();
			JSONObject count = new JSONObject();
			JSONObject rule = new JSONObject();
			
			List<Node> nodeName = new ArrayList<>();
			Node currentNode;
//			parentStatistics.put("children", new JSONArray());
//			parentStatistics.put("rules", new JSONArray());
//			parentStatistics.put("depth", new JSONArray());
			
			
			
			ruleStatistics=getNodeStatistics(n);
			count=getRuleCount(n,rule);
			
			nodeName=compressNodeName(n);
			if(nodeName.size() >= 1 ) {
				parentJson.put("size",nodeName.size());
				parentJson.put("rulesCount",count);
				parentJson.put("name",nodeNum++);
				parentJson.put("displayName",n.name()+','+nodeName.get(nodeName.size()-1).name());
//				System.out.println(ruleStatistics);
				parentJson.put("statistics",ruleStatistics);
				currentNode= nodeName.get(nodeName.size()-1);
			}
			else {
				parentJson.put("size",n.childrenCount());
				parentJson.put("name",nodeNum++);
				parentJson.put("displayName",n.name());
				currentNode=n;
			}
			treeDepthList.add(ruleStatistics.getJSONObject("branchDepth").getDouble("avgMax"));
			treeTimeList.add(ruleStatistics.getDouble("branchTime"));
			parentName.clear();
			ruleCount=0;
		
			if (currentNode.childrenCount() > 0) {
				parentJson.put("children", new JSONArray());
			}
			
			for(int i=0;i<currentNode.childrenCount();i++) {
				parentJson.accumulate("children", treeBasedOnNodeName(currentNode.child(i)));	
			}
			return parentJson;
		}	
	}
	
	public static JSONArray branchDepthStatistics(Node n) throws JSONException {
		JSONObject parentJson = new JSONObject();
		if(n.childrenCount()==0) {
			parentJson.put("name",branchNum++);
			parentJson.put("depth", 0);
			jsonDepth.put(parentJson);
			return jsonDepth;
		}
		else {
			
			JSONObject ruleStatistics = new JSONObject();
			List<Node> nodeName = new ArrayList<>();
			Node currentNode;
			ruleStatistics=getNodeStatistics(n);
			nodeName=compressNodeName(n);
			if(nodeName.size() >= 1 ) {
				parentJson.put("name",branchNum++);
				parentJson.put("depth",ruleStatistics.getJSONObject("branchDepth").get("avgMax"));
				parentJson.put("displayName",n.name()+','+nodeName.get(nodeName.size()-1).name());
				currentNode= nodeName.get(nodeName.size()-1);
			}
			else {
				parentJson.put("name",branchNum++);
				parentJson.put("displayName",n.name());
				currentNode=n;
			}
			parentName.clear();
			ruleCount=0;
			jsonDepth.put(parentJson);
			for(int i=0;i<currentNode.childrenCount();i++){
				branchDepthStatistics(currentNode.child(i));	
			}
			return jsonDepth;
		}	
	}
	public static List<Node> compressNodeName(Node n) {
		if(n.childrenCount()==1 && !n.leaf()) {
			parentName.add(n.child(0));
			compressNodeName(n.child(0));
		}	
			return parentName;
	}
	
	
	public static JSONObject getRuleCount(Node n,JSONObject rule ) throws JSONException {	
		if(n.childrenCount()>=1 && !n.leaf()) {
			Rule r = n.getAppliedRuleApp().rule();
//			System.out.println(n.name());
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					long count = 1;		
					Object value = rule.has(rs.name().toString()) ?
							rule.get(rs.name().toString()) : null;
					if (value instanceof Long) {
						count = ((Long)value) + 1;
					} else if (value != null) {
						throw new IllegalStateException();
					}
					
					rule.put(rs.name().toString(), count);
				}
				if(n.childrenCount()==1) {
					getRuleCount(n.child(0),rule);
				}
				 
			}
		}
		return rule;
	}
	
	public static JSONObject getNodeStatistics(Node n) throws JSONException {
		JSONObject parent = new JSONObject();
		List<Double> doubleBranchDepth = new ArrayList<>();
		List<Double> doubleNodeDepth = new ArrayList<>();
		List<Double> doubleBranchTime = new ArrayList<>();
		JSONObject rootNodeObject = new JSONObject();
		parent.put("name", n.name());
		rootNodeObject=getRootNodeDepth(n);
		doubleNodeDepth.add(rootNodeObject.getJSONObject("nodeDepth").getDouble("avgMax"));
		doubleBranchDepth.add(rootNodeObject.getJSONObject("nodeDepth").getDouble("total"));
		parent.put("nodeDepth", rootNodeObject.getJSONObject("nodeDepth"));
		parent.put("rules", rootNodeObject.get("rules"));
		parent.put("id", n.serialNr());
		doubleBranchTime.add((double)n.getCreationTime());
		System.out.println(n.getCreationTime());
		if(n.childrenCount()>=1 && !n.leaf()) {	
				int k=0;
				for(int i=0;i<=k;i++) {
					List<String> ruleNameList = new ArrayList<>();
					String ruleName;
					JSONObject childJson = new JSONObject();
					childJson.put("name", n.child(0).name());
					childJson.put("id",n.child(0).serialNr());
					
			
					if(!n.child(0).leaf()) {
						Rule r = n.child(0).getAppliedRuleApp().rule();
						if (r instanceof Taclet) {
							Taclet t = (Taclet) r;
							for(RuleSet rs : t.getRuleSets()) {
								ruleNameList.add(rs.name().toString());
							}
							ruleName = ruleNameList.toString().replace("[", "").replace("]", "");
							childJson.put("rules",ruleName);	
						
						}
					}
					else
					{
						childJson.put("rules","null");
					}
					Iterator<SequentFormula> it = n.child(0).sequent().iterator();
					List<Double> doubleDepth = new ArrayList<>();
					JSONObject depthJson = new JSONObject();
					while(it.hasNext()) {
			            SequentFormula cf = it.next();
			            doubleDepth.add(Double.valueOf(cf.formula().depth()));
			            
			        }
					depthJson = countNodeDepth(doubleDepth);
					childJson.put("nodeDepth",depthJson);
					doubleNodeDepth.add(depthJson.getDouble("avgMax"));
					doubleBranchDepth.add(depthJson.getDouble("total"));				
					doubleBranchTime.add((double)n.child(0).getCreationTime());
					if (n.child(0).childrenCount()==1) {
						k++;
						n=n.child(0);
					}
					parent.accumulate("children",childJson);				
				}
				JSONObject branchDepthJson = new JSONObject();
				JSONObject timeJosn = new JSONObject();
			
				timeJosn=countMinMax(doubleBranchTime);
				double time=timeJosn.getDouble("max") - timeJosn.getDouble("min");
				float seconds = (float)((time)/ 1000);
				
				branchDepthJson = countNodeDepth(doubleBranchDepth);
				branchDepthJson.put("avgMaxDetails", countNodeDepth(doubleNodeDepth));
				parent.put("branchTime",seconds );
				parent.put("branchDepth",branchDepthJson );
	
				
		
		}
		return parent;
	}
	public static JSONObject getRootNodeDepth(Node n) throws JSONException {
		JSONObject rootNodeObject = new JSONObject();
		List<String> ruleNameList = new ArrayList<>();
		String ruleName;
			Rule r = n.getAppliedRuleApp().rule();
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					ruleNameList.add(rs.name().toString());
				}
				ruleName = ruleNameList.toString().replace("[", "").replace("]", "");
				rootNodeObject.put("rules",ruleName);	
	
			}
			else {
				rootNodeObject.put("rules","null");	
			}
		Iterator<SequentFormula> it = n.child(0).sequent().iterator();
		List<Double> doubleDepth = new ArrayList<>();
		JSONObject depthJson = new JSONObject();
		while(it.hasNext()) {
            SequentFormula cf = it.next();
            doubleDepth.add(Double.valueOf(cf.formula().depth()));
            
        }
		depthJson = countNodeDepth(doubleDepth);
		rootNodeObject.put("nodeDepth",depthJson);				
		System.out.println(rootNodeObject);
		
		return rootNodeObject;
	}
	
	public static JSONObject countNodeDepth(List<Double> depth) throws JSONException {
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
        depthObject.put("avgMax", avgMax);
        depthObject.put("total", total);
        return depthObject;
	}
	
	public static JSONObject TreeBasedOnRule(Node n) throws JSONException {
		if(n.childrenCount()==0) {
			JSONObject childJson = new JSONObject();
			if(!n.leaf()) {
				Rule r = n.getAppliedRuleApp().rule();
				Taclet t = (Taclet) r;
				childJson.put("size",1);
				childJson.put("name",t.ruleSets().next().name());
			}
			else {
				childJson.put("size",1);
				childJson.put("name", n.name());
			}
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			Node nodeName;
			Node currentNode = null;
			List<String> ruleNameList = new ArrayList<>();
			String ruleName;
			nodeName=compressNodeRule(n);
			if(nodeName != null) {
				Rule r = nodeName.getAppliedRuleApp().rule();
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					ruleNameList.add(rs.name().toString());
				}
				ruleName = ruleNameList.toString().replace("[", "").replace("]", "");
				parentJson.put("size",ruleNodeSize);
				parentJson.put("name",ruleName);
				currentNode= nodeName;
				ruleNode=null;
				ruleNodeSize=0;
			}
			else if(!n.leaf() ){
				Rule r = n.getAppliedRuleApp().rule();
				if (r instanceof Taclet) {
					Taclet t = (Taclet) r;
					parentJson.put("size",n.childrenCount());
					parentJson.put("name",t.ruleSets().next().name());
					currentNode= n;
				}
				else {
					parentJson.put("size",n.childrenCount());
					parentJson.put("name",n.name());
					currentNode= n;
				}
			}
			
			if (n.childrenCount() > 0) {	
				parentJson.put("children", new JSONArray());
			}
			for(int i=0;i<n.childrenCount();i++) {
				parentJson.accumulate("children", TreeBasedOnRule(currentNode.child(i)));
			}
			return parentJson;
		}	
	}
	
	public static Node compressNodeRule(Node n) {
		if(n.childrenCount()==1 && !n.leaf()) {
			Rule r = n.getAppliedRuleApp().rule();
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				if((t.ruleSets().next().name()).toString() == ruleName || ruleName==null){
					ruleName=(t.ruleSets().next().name()).toString();
					ruleNode=n;
					compressNodeRule(ruleNode.child(0));
					ruleNodeSize++;
				}
			}
			else {
				ruleNode=null;
			}
		}
		return ruleNode;
	}
	
	public static JSONObject countMinMax(List<Double> numList) throws JSONException{
		double max = numList.get(0);
        double min = numList.get(0);
        for (int counter = 1; counter < numList.size(); counter++)
        {
         if (numList.get(counter) > max)
         {
          max = numList.get(counter);
         
         }
         if (numList.get(counter) < min)
         {
        	 min = numList.get(counter);
         }
        }
        JSONObject minMaxJson = new JSONObject();
        minMaxJson.put("max", max);
        minMaxJson.put("min", min);
		return minMaxJson;
	}
	
	public static void main(String[] args) throws IOException, JSONException {
        System.out.println("Welcome to the ProofProfiler!");
        try {
        	if( 0 < args.length ) {
        		if( args[0].equals("simple") ) {
        			ProofLoader proofLoader = new ProofLoader(PATH);
        			Proof proof = proofLoader.getProof();
        			JSONObject treeBasedOnNodeName = new JSONObject();
        			JSONObject minMaxDepth = new JSONObject();
        			JSONObject minMaxTime = new JSONObject();
        			treeBasedOnNodeName= treeBasedOnNodeName(proof.root());
        			minMaxDepth = countMinMax(treeDepthList);
        			treeBasedOnNodeName.put("TreeDepth", minMaxDepth);
//        			minMaxTime = countMinMax(treeTimeList);
//        			treeBasedOnNodeName.put("TreeTime", minMaxTime);
        			String nodeTree=(treeBasedOnNodeName).toString();
//        			String ruleTree=(TreeBasedOnRule(proof.root())).toString();
        			String fullTree=(toJSON(proof.root())).toString();
        			String branchDepth=(branchDepthStatistics(proof.root())).toString();
        			
//        			String fullTreeToJson=(fullTreeToJson(proof.root())).toString();
        			File file = new File("identity.json");
        			FileOutputStream fos = new FileOutputStream(file);
        			BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(fos));
        			//bw.write("Node Tree-");
        			bw.write(nodeTree);
        			bw.newLine();
        			//bw.write("Rule tree-");
//        			bw.write(ruleTree);
        			bw.write(fullTree);
        			Profiler profiler = new StatisticsProfiler();
					ProfilingData data = profiler.profile(proof);
					Gson g = new Gson();
					String proofstr = g.toJson(data);
//					bw.newLine();
//					bw.write(fullTreeToJson);
					bw.newLine();
					bw.write(branchDepth);
					bw.newLine();
					bw.write(proofstr);
        			bw.close();
        			
        			
            	}
        	}
        } catch (Throwable e) {
			e.printStackTrace();
		}
    }
}