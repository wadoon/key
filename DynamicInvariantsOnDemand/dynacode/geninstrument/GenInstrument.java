package geninstrument;
import java.util.ArrayList;
import java.util.HashMap;

public class GenInstrument implements IGenInstrument {
public HashMap<String, ArrayList<Integer>> callGenInstrument(ArrayList<Integer> inputVariables)
{
HashMap<String, ArrayList<Integer>> varLoopHeadTraces = new HashMap<String, ArrayList<Integer>>();
int n = inputVariables.get(0);
int _n = n;
int r = 0;
int i = 0;
ArrayList<Integer> traces__n = new ArrayList<Integer>();
ArrayList<Integer> traces_n = new ArrayList<Integer>();
ArrayList<Integer> traces_r = new ArrayList<Integer>();
ArrayList<Integer> traces_i = new ArrayList<Integer>();
varLoopHeadTraces.put("_n",traces__n);
varLoopHeadTraces.put("n",traces_n);
varLoopHeadTraces.put("r",traces_r);
varLoopHeadTraces.put("i",traces_i);
while ( i<_n ) {traces__n.add(_n);
traces_n.add(n);
traces_r.add(r);
traces_i.add(i);
   int j = 0;                         while ( j<_n ) {     r=r+1;     j=j+1;   }   i=i+1; }
return varLoopHeadTraces;
}
}