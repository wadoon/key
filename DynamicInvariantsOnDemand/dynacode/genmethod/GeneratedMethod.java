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
ArrayList<Integer> beforeLoop__x = new ArrayList<Integer>();
ArrayList<Integer> beforeLoop_y = new ArrayList<Integer>();
ArrayList<Integer> beforeLoop_z = new ArrayList<Integer>();
while ( y>0 ) {   z=z+_x;   y=y-1; }
int afterLoop__x = _x;
int afterLoop_y = y;
int afterLoop_z = z;
generatedMethodReturnObject.beginLoopTraces.add(beforeLoop__x);
generatedMethodReturnObject.beginLoopTraces.add(beforeLoop_y);
generatedMethodReturnObject.beginLoopTraces.add(beforeLoop_z);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop__x);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop_y);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop_z);
generatedMethodReturnObject.originalReturnValue = z;
return generatedMethodReturnObject;
}
}