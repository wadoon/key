/**
 * 
 */
package recoder.testsuite.testsuite;

import java.io.IOException;

import junit.framework.TestSuite;
import recoder.testsuite.testsuite.exhaustive.ReadJDKSources;

/**
 * @author Tobias Gutzmann
 *
 */
public class ExhaustiveTestSuite extends CompleteTestSuite {
	public ExhaustiveTestSuite() throws IOException, ClassNotFoundException,
			IllegalAccessException, InstantiationException {
		super();
		addTestSuite(ReadJDKSources.class);
	}

    public static TestSuite suite() throws IOException, ClassNotFoundException, IllegalAccessException, InstantiationException {
        return new ExhaustiveTestSuite();
    }
}
