package genmethod;
import java.util.ArrayList;
import java.util.HashMap;

public class GeneratedMethod implements IGeneratedMethod {
public HashMap<String, ArrayList<Integer>> callGeneratedMethod(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int b = inputVariables.get(0);
int a = inputVariables.get(1);
int _b = b;
int r = a;
int j = 0;
ArrayList<Integer> traces__b = new ArrayList<Integer>();
ArrayList<Integer> traces_b = new ArrayList<Integer>();
ArrayList<Integer> traces_r = new ArrayList<Integer>();
ArrayList<Integer> traces_a = new ArrayList<Integer>();
ArrayList<Integer> traces_j = new ArrayList<Integer>();
varLoopHeadTraces.put("_b",traces__b);
varLoopHeadTraces.put("b",traces_b);
varLoopHeadTraces.put("r",traces_r);
varLoopHeadTraces.put("a",traces_a);
varLoopHeadTraces.put("j",traces_j);
while ( j<_b ) {traces__b.add(_b);
traces_b.add(b);
traces_r.add(r);
traces_a.add(a);
traces_j.add(j);
   r=r+1;   j=j+1; }
return varLoopHeadTraces;
}
}