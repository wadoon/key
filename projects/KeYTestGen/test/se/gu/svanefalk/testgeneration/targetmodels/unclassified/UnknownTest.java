package se.gu.svanefalk.testgeneration.targetmodels.unclassified;


public class UnknownTest {
	private UnknownTest next;
	
	private UnknownTest previous;
	
	public UnknownTest main() {
		previous = null;
		next = new UnknownTest();
		next.next = new UnknownTest();
		return next.next;
	}
}
