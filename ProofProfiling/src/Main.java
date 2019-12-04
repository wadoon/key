import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.List;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import io.ProofLoader;
import profiling.Profiler;
import profiling.ProfilingData;
import profiling.statistics.StatisticsProfiler;
import com.google.gson.*;
public class Main {

	final static String PATH = "C:\\Users\\shiva\\git\\key\\key\\key.ui\\examples\\standard_key\\prop_log\\proof\\allClausesLength4.key.proof";
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
	public static List<Long> treeTimeList = new ArrayList<>();
	public static JSONArray jsonDepth = new JSONArray();
	
	public static JSONObject treeBasedOnNodeName(Node n) throws JSONException {
		if(n.childrenCount()==0) {
			JSONObject childJson = new JSONObject();
			childJson.put("size",20);
			childJson.put("name",nodeNum++);
			childJson.put("displayName", n.name());
			return childJson;
		}
		else {
			JSONObject parentJson = new JSONObject();
			JSONObject ruleStatistics = new JSONObject();
			JSONObject count = new JSONObject();
			JSONObject rule = new JSONObject();
			JSONObject ruleTime = new JSONObject();
			List<Node> nodeName = new ArrayList<>();
			Node currentNode;
			
			timeCollector timeCollector= new timeCollector();
			Statistics statistics=new Statistics();
			ruleCollector ruleCollector= new ruleCollector();
			
			ruleStatistics=statistics.getStatistics(n);
			nodeName=compressNodeName(n);
			System.out.println(count);
			if(nodeName.size() >= 1 ) {
				parentJson.put("size",20);
				parentJson.put("rulesCount",ruleCollector.getRuleCount(n,rule));
				parentJson.put("name",nodeNum++);
				parentJson.put("displayName",n.name()+','+nodeName.get(nodeName.size()-1).child(0).name());
				parentJson.put("statistics",ruleStatistics);
				parentJson.put("rulesTime",timeCollector.getRuleTime(n, ruleTime));
				currentNode= nodeName.get(nodeName.size()-1).child(0);
			}
			else {
				parentJson.put("size",20);
				parentJson.put("name",nodeNum++);
				parentJson.put("displayName",n.name());
				currentNode=n;
			}
			
			treeDepthList.add(ruleStatistics.getJSONObject("branchNodeDepthDetails").getDouble("avg"));
			treeTimeList.add(ruleStatistics.getJSONObject("branchNodeTimeDetails").getLong("total"));
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
			parentName.add(n);
			compressNodeName(n.child(0));
					
		}		
		return parentName;
	}
	
	public static void main(String[] args) throws IOException, JSONException {
        System.out.println("Welcome to the ProofProfiler!");
        try {
        	if( 0 < args.length ) {
        		if( args[0].equals("simple") ) {
        			ProofLoader proofLoader = new ProofLoader(PATH);
        			depthCollector depthCollector = new depthCollector();
        			timeCollector timeCollector= new timeCollector();
        			correlation correlation = new correlation();
        			
        			Proof proof = proofLoader.getProof();
        			JSONObject treeBasedOnNodeName = new JSONObject();
        			treeBasedOnNodeName= treeBasedOnNodeName(proof.root());
        			treeBasedOnNodeName.put("TreeDepth", depthCollector.countDepth(treeDepthList));
        			treeBasedOnNodeName.put("TreeTime", timeCollector.countTime(treeTimeList));
        			treeBasedOnNodeName.put("TreeFullTime", treeTimeList);
        			treeBasedOnNodeName.put("TreeFullDepth", treeDepthList);
        			String nodeTree=(treeBasedOnNodeName).toString();
        			correlation.correlationStatitics(treeDepthList,treeTimeList);
        			File file = new File("identity.json");
        			FileOutputStream fos = new FileOutputStream(file);
        			BufferedWriter bw = new BufferedWriter(new OutputStreamWriter(fos));
        			bw.write(nodeTree);
        			bw.newLine();
        			Profiler profiler = new StatisticsProfiler();
					ProfilingData data = profiler.profile(proof);
					Gson g = new Gson();
					String proofstr = g.toJson(data);
					bw.write(proofstr);
        			bw.close();
            	}
        	}
        } catch (Throwable e) {
			e.printStackTrace();
		}
    }
}