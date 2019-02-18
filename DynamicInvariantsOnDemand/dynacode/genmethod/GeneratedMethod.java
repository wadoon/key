package genmethod;
import java.util.ArrayList;
import java.util.HashMap;

public class GeneratedMethod implements IGeneratedMethod {
public HashMap<String, ArrayList<Integer>> callGeneratedMethod(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int x = inputVariables.get(0);
int y = inputVariables.get(1);
int q = 0;
int r = x;
int _x = x;
int _y = y;
ArrayList<Integer> traces__y = new ArrayList<Integer>();
ArrayList<Integer> traces__x = new ArrayList<Integer>();
ArrayList<Integer> traces_r = new ArrayList<Integer>();
ArrayList<Integer> traces_q = new ArrayList<Integer>();
varLoopHeadTraces.put("q",traces__y);
varLoopHeadTraces.put("r",traces__x);
varLoopHeadTraces.put("_x",traces_r);
varLoopHeadTraces.put("_y",traces_q);
while ( _y<=r ) {   int a = 1;   int b = _y;                         while ( 2*b<=r ) {traces__y.add(q);
traces__x.add(r);
traces_r.add(_x);
traces_q.add(_y);
     a=2*a;     b=2*b;   }   r=r-b;   q=q+a; }
return varLoopHeadTraces;
}
}