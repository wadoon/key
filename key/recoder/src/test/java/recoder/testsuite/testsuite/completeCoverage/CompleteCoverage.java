package recoder.testsuite.testsuite.completeCoverage;

import junit.framework.Test;
import junit.framework.TestSuite;

public class CompleteCoverage {

	public static Test suite() {
		TestSuite suite = new TestSuite(
				"Test for recoder.testsuite.completeCoverage");
		//$JUnit-BEGIN$
		suite.addTestSuite(NameInfoCoverage.class);
		//$JUnit-END$
		return suite;
	}

}
