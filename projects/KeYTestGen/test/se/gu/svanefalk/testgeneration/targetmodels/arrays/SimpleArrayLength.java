package se.gu.svanefalk.testgeneration.targetmodels.arrays;

public class SimpleArrayLength {
	public int compute(Object[] array) {
		if (array.length == 1) {
			return 42;
		}
		else {
			return -100;
		}
	}
}
