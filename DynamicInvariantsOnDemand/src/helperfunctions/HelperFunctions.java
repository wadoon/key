package helperfunctions;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public final class HelperFunctions {
	private HelperFunctions() {}
	
	public static HashMap<String, ArrayList<Integer>> mergeMapsKeyWise(HashMap<String, ArrayList<Integer>> map1, HashMap<String, ArrayList<Integer>> map2) {
		HashMap<String, ArrayList<Integer>> mergedMap = new HashMap<String, ArrayList<Integer>>(map1);
		
		if (mergedMap.isEmpty()) {
			mergedMap.putAll(map2);
		}
		else {
			for (Entry<String, ArrayList<Integer>> entry : mergedMap.entrySet()) {
			    for (Entry<String, ArrayList<Integer>> entry2 : map2.entrySet()) {
			        if (entry.getKey().equals(entry2.getKey())) {
			            entry.getValue().addAll(entry2.getValue());
			        }
			    }
			}
		}
		return mergedMap;
	}
	
	public static boolean isInteger(String strInt) {
	    try {
	        int i = Integer.parseInt(strInt);
	    } catch (NumberFormatException | NullPointerException nfe) {
	        return false;
	    }
	    return true;
	}
	
	public static String formatTracesToDIG(HashMap<String, ArrayList<Integer>> varTraces) {
		StringBuilder sb = new StringBuilder();
		
		//FIXME: sage works with first sign alphanumeric variables, thus conversion: _x -> u_x
		//Write Var. line: "u_x y q a b r"
		int i = 0;
		for (String varName : varTraces.keySet()) {
			if (i != 0)
				sb.append(" ");
			String varNameWithoutUnderscore = varName.replaceFirst("^_", "u_");
			sb.append(varNameWithoutUnderscore);
			i++;
		}
		sb.append(System.lineSeparator());
		
		ArrayList<ArrayList<Integer>> values = new ArrayList<ArrayList<Integer>>();
		for (Map.Entry<String, ArrayList<Integer>> e : varTraces.entrySet()) {
			values.add(e.getValue());
		}
		
		for (int j = 0; j < values.get(0).size(); j++) {
			for (int k = 0; k < values.size(); k++) {
				sb.append(values.get(k).get(j));
				sb.append(" ");
			}
			sb.append(System.lineSeparator());
		}
		
		return sb.toString();
	}
	
	public static void writeStringToFile(String content, String fileDest) {
	    try {
	    	BufferedWriter writer = new BufferedWriter(new FileWriter(fileDest));
			writer.write(content);
			writer.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}