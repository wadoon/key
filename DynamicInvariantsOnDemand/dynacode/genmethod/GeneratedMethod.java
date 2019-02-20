package genmethod;
import java.util.ArrayList;
import java.util.HashMap;

public class GeneratedMethod implements IGeneratedMethod {
public HashMap<String, ArrayList<Integer>> callGeneratedMethod(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int x = inputVariables.get(0);
int _x = x;
int y = x;
int z = 0;
ArrayList<Integer> traces__x = new ArrayList<Integer>();
ArrayList<Integer> traces_z = new ArrayList<Integer>();
ArrayList<Integer> traces_y = new ArrayList<Integer>();
varLoopHeadTraces.put("_x",traces__x);
varLoopHeadTraces.put("y",traces_z);
varLoopHeadTraces.put("z",traces_y);
while ( y>0 ) {traces__x.add(_x);
traces_z.add(y);
traces_y.add(z);
   z=z+_x;   y=y-1; }
return varLoopHeadTraces;
}
}