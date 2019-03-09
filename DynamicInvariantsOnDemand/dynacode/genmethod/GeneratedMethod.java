package genmethod;
import java.util.ArrayList;
import java.util.HashMap;

public class GeneratedMethod implements IGeneratedMethod {
public HashMap<String, ArrayList<Integer>> callGeneratedMethod(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int y = inputVariables.get(0);
int _y = y;
int q = 0;
int r = x;
ArrayList<Integer> traces__y = new ArrayList<Integer>();
ArrayList<Integer> traces_q = new ArrayList<Integer>();
ArrayList<Integer> traces_r = new ArrayList<Integer>();
varLoopHeadTraces.put("_y",traces__y);
varLoopHeadTraces.put("q",traces_q);
varLoopHeadTraces.put("r",traces_r);
while ( _y<=r ) {   int a = 1;   int b = _y;                         while ( 2*b<=r ) {traces__y.add(_y);
traces_q.add(q);
traces_r.add(r);
     a=2*a;     b=2*b;   }   r=r-b;   q=q+a; }
return varLoopHeadTraces;
}
}