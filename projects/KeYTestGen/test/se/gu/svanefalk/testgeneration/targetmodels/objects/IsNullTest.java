package se.gu.svanefalk.testgeneration.targetmodels.objects;

public class IsNullTest {
	public static int compute(IsNullTest obj) {
		if (obj == null) {
			return 1;
		}
		else {
			return 0;
		}
	}
}
