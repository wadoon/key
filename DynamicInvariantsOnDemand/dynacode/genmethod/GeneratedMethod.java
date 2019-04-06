package genmethod;
import java.util.ArrayList;
import java.util.HashMap;

public class GeneratedMethod implements IGeneratedMethod {
public HashMap<String, ArrayList<Integer>> callGeneratedMethod(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int y = inputVariables.get(0);
int q_0 = inputVariables.get(1);
int r_0 = inputVariables.get(2);
int _y = y;
int q = q_0;
int r = r_0;
int a = 1;
int b_2 = y;
ArrayList<Integer> traces__y = new ArrayList<Integer>();
ArrayList<Integer> traces_y = new ArrayList<Integer>();
ArrayList<Integer> traces_q = new ArrayList<Integer>();
ArrayList<Integer> traces_q_0 = new ArrayList<Integer>();
ArrayList<Integer> traces_r = new ArrayList<Integer>();
ArrayList<Integer> traces_r_0 = new ArrayList<Integer>();
ArrayList<Integer> traces_a = new ArrayList<Integer>();
ArrayList<Integer> traces_b_2 = new ArrayList<Integer>();
varLoopHeadTraces.put("_y",traces__y);
varLoopHeadTraces.put("y",traces_y);
varLoopHeadTraces.put("q",traces_q);
varLoopHeadTraces.put("q_0",traces_q_0);
varLoopHeadTraces.put("r",traces_r);
varLoopHeadTraces.put("r_0",traces_r_0);
varLoopHeadTraces.put("a",traces_a);
varLoopHeadTraces.put("b_2",traces_b_2);
while ( 2*b_2<=r ) {traces__y.add(_y);
traces_y.add(y);
traces_q.add(q);
traces_q_0.add(q_0);
traces_r.add(r);
traces_r_0.add(r_0);
traces_a.add(a);
traces_b_2.add(b_2);
   a=2*a;   b_2=2*b_2; }
return varLoopHeadTraces;
}
}