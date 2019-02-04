package helperfunctions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public final class HelperFunctions {
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
}
