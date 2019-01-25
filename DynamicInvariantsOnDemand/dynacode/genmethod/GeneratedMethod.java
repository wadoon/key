package genmethod;
import java.util.ArrayList;
public class GeneratedMethod implements IGeneratedMethod {
public GeneratedMethodReturnObject callGeneratedMethod(ArrayList<Integer> inputVariables)
{
GeneratedMethodReturnObject generatedMethodReturnObject = new GeneratedMethodReturnObject();
int y = heap;
int z = 0;
ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
ArrayList<Integer> beginLoop_z = new ArrayList<Integer>();
while ( y>0 ) {beginLoop_y.add(y);
beginLoop_z.add(z);
   z=z+this.x;   y=y-1; }
int afterLoop_y = y;
int afterLoop_z = z;
generatedMethodReturnObject.beginLoopTraces.add(beginLoop_y);
generatedMethodReturnObject.beginLoopTraces.add(beginLoop_z);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop_y);
generatedMethodReturnObject.afterLoopTraces.add(afterLoop_z);
generatedMethodReturnObject.originalReturnValue = z;
return generatedMethodReturnObject;
}
}