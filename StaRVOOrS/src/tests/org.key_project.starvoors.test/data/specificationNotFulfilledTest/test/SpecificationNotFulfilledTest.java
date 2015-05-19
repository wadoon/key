
public class SpecificationNotFulfilledTest {
	/*@ normal_behavior
	  @ requires true;
	  @ ensures true;
	  @*/
	public static int main(/*@ nullable @*/ SpecificationNotFulfilledTest obj, int value, int z) {
		if (value == 1) {
			return obj.magic(-4711);
		}
		else if (value == 2) {
			/*@ loop_invariant z >= 2;
			  @ decreasing value;
			  @*/
			while (z > 2) {
				z--;
			}
			return 2;
		}
		else {
			return 0;
		}
	}
	
	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures \result == 42;
	  @*/
	public int magic(int x) {
		return 42;
	}
}
