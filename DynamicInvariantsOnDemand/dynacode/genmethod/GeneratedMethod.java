package genmethod;
import java.util.ArrayList;
public class GeneratedMethod implements IGeneratedMethod {
public GeneratedMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables)
{
GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
int x = inputVariables.get(0);
int _x = x;
int y = x;
int z = 0;
ArrayList<Integer> beginLoop__x = new ArrayList<Integer>();
ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
ArrayList<Integer> beginLoop_z = new ArrayList<Integer>();
while ( y>0 ) {beginLoop__x.add(_x);
beginLoop_y.add(y);
beginLoop_z.add(z);
   z=z+_x;   y=y-1; }
int afterLoop__x = _x;
int afterLoop_y = y;
int afterLoop_z = z;
generatedMethodReturnObject.beginLoopTraces.add(beginLoop__x);
generatedMethodReturnObject.beginLoopTraces.add(beginLoop_y);
generatedMethodReturnObject.beginLoopTraces.add(beginLoop_z);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop__x);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop_y);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop_z);
generatedMethodReturnObject.originalReturnValue = z;
return generatedMethodReturnObject;
}
}