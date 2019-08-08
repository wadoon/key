import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import io.ProofLoader;
import profiling.Profiler;
import profiling.ProfilingData;
import profiling.nodecount.NodeCountProfiler;
import profiling.statistics.StatisticsProfiler;
import com.google.gson.*;
import com.sun.xml.internal.bind.v2.runtime.RuntimeUtil.ToStringAdapter;
import com.sun.xml.internal.fastinfoset.util.StringArray;
public class Main {

	final static String PATH = "C:\\key workspace\\key\\key\\key.ui\\examples\\standard_key\\prop_log\\proof\\allClausesLength4.key.proof";
	public static List<Node> parentName = new ArrayList<>();
	public static String ruleName;
	public static Node ruleNode;
	public static int ruleNodeSize=0;
	public static int ruleCount=0;
	public static int nodeNumber=0;
	public static int endnode=0;
	public static JSONObject rule = new JSONObject();
	
	public static JSONObject toJSON(Node n) throws JSONException {
		if(n.childrenCount()==0) {
			JSONObject childJson = new JSONObject();
			childJson.put("name", n.name());
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			parentJson.put("name", n.name());
			if (n.childrenCount() > 0) {
				parentJson.put("children", new JSONArray());
			}
			for(int i=0;i<n.childrenCount();i++) {
				parentJson.accumulate("children", toJSON(n.child(i)));	
			}
			return parentJson;
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
			childJson.put("size",1);
			childJson.put("name", n.name());
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			JSONObject count = new JSONObject();
			List<Node> nodeName = new ArrayList<>();
			Node currentNode;
			count=getRuleCount(n);
			System.out.println(count);
			nodeName=compressNodeName(n);
			if(nodeName.size() > 1 ) {
				parentJson.put("size",nodeName.size());
				parentJson.put("rules",count);
			
				parentJson.put("name",n.name()+','+nodeName.get(nodeName.size()-1).name());
				currentNode= nodeName.get(nodeName.size()-1);
			}
			else {
				parentJson.put("size",n.childrenCount());
				parentJson.put("name",n.name());
				currentNode=n;
			}
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
	public static List<Node> compressNodeName(Node n) {
		if(n.childrenCount()==1 && !n.leaf()) {
			parentName.add(n.child(0));
			compressNodeName(n.child(0));
		}	
			return parentName;
	}
	
	public static JSONObject getRuleCount(Node n) throws JSONException {	
		if(n.childrenCount()==1 && !n.leaf()) {
			Rule r = n.getAppliedRuleApp().rule();
			if (r instanceof Taclet) {
				Taclet t = (Taclet) r;
				for(RuleSet rs : t.getRuleSets()) {
					rule.put(rs.name().toString(),++ruleCount);
				}
				getRuleCount(n.child(0));
			}
		}
		return rule;
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
	
	public static void main(String[] args) throws IOException, JSONException {
        System.out.println("Welcome to the ProofProfiler!");
        try {
        	if( 0 < args.length ) {
        		if( args[0].equals("simple") ) {
        			ProofLoader proofLoader = new ProofLoader(PATH);
        			Proof proof = proofLoader.getProof();
        			
        			String nodeTree=(treeBasedOnNodeName(proof.root()).toString());
        			String ruleTree=(TreeBasedOnRule(proof.root())).toString();
        			String fullTree=(toJSON(proof.root())).toString();
//        			String fullTreeToJson=(fullTreeToJson(proof.root())).toString();
        			File file = new File("identity.json");
        			FileOutputStream fos = new FileOutputStream(file);
        			BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(fos));
        			//bw.write("Node Tree-");
        			bw.write(nodeTree);
        			bw.newLine();
        			//bw.write("Rule tree-");
        			bw.write(ruleTree);
        			bw.newLine();
        			bw.write(fullTree);
        			Profiler profiler = new StatisticsProfiler();
					ProfilingData data = profiler.profile(proof);
					Gson g = new Gson();
					String proofstr = g.toJson(data);
//					bw.newLine();
//					bw.write(fullTreeToJson);
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