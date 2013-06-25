package se.gu.svanefalk.testgeneration.targetmodels.arrays;

public class ObjectArrayIndexReadAccess {
	public static int compute(IntWrapper[] array) {
		if (array != null) {
			if (array.length == 1) {
				if (array[0].value == 42) {
					return 42;
				}
				else {
					return -300;
				}
			}
			else {
				return -200;
			}
		}
		else {
			return -100;
		}
	}
}

class IntWrapper {
	public int value;
}