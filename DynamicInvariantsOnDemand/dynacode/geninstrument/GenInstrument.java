package geninstrument;
import java.util.ArrayList;
import java.util.HashMap;

public class GenInstrument implements IGenInstrument {
public HashMap<String, ArrayList<Integer>> callGenInstrument(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int i_0 = inputVariables.get(0);
int _n = i_0;
int r = i_0;
int j = 0;
ArrayList<Integer> traces__n = new ArrayList<Integer>();
ArrayList<Integer> traces_i_0 = new ArrayList<Integer>();
ArrayList<Integer> traces_r = new ArrayList<Integer>();
ArrayList<Integer> traces_j = new ArrayList<Integer>();
varLoopHeadTraces.put("_n",traces__n);
varLoopHeadTraces.put("i_0",traces_i_0);
varLoopHeadTraces.put("r",traces_r);
varLoopHeadTraces.put("j",traces_j);
while ( j<_n ) {traces__n.add(_n);
traces_i_0.add(i_0);
traces_r.add(r);
traces_j.add(j);
   r=r+1;   j=j+1; }
return varLoopHeadTraces;
}
}