/**
 * 
 */
package recoder.testsuite.testsuite.semantics;

import java.util.ArrayList;
import java.util.EventObject;
import java.util.List;

import junit.framework.TestCase;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.ParserException;
import recoder.java.CompilationUnit;
import recoder.service.DefaultErrorHandler;
import recoder.service.ErrorHandler;
import recoder.service.SemanticsChecker;
import recoder.service.TypingException;

/**
 * @author Tobias Gutzmann
 *
 */
public class SemanticsChecks extends TestCase {
	// TODO evil copy & paste from FixedBugs, with some adaptions...
	
	////////////////////////////////////////////////////////////
	// helper methods / classes
	////////////////////////////////////////////////////////////
    private CrossReferenceServiceConfiguration sc;
	private List<CompilationUnit> runIt(String ... cuTexts) throws ParserException {
		return runIt(null, cuTexts);
	}

	private List<CompilationUnit> runIt(ErrorHandler eh, String ... cuTexts) throws ParserException {
		sc = new CrossReferenceServiceConfiguration();
		sc.getProjectSettings().setErrorHandler(new ThrowingErrorHandler());
       	sc.getProjectSettings().ensureSystemClassesAreInPath();
       	ArrayList<CompilationUnit> cus = new ArrayList<CompilationUnit>();
       	for (String cuText : cuTexts) {
       		CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
       		sc.getChangeHistory().attached(cu);
       		cus.add(cu);
       	}
       	if (eh != null)
       		sc.getProjectSettings().setErrorHandler(eh);
       	sc.getChangeHistory().updateModel();
       	for (CompilationUnit cu : cus)
       		cu.validateAll();
        return cus;
	}

	private static class ThrowingErrorHandler extends DefaultErrorHandler {
		@Override
		public void reportError(Exception e) {
			throw (ModelException)e;
		}
	}
	
	private static class SilentErrorHandler extends DefaultErrorHandler {
		private final int exp;
		private int errCnt = 0;
		SilentErrorHandler(int cnt) {
			exp = cnt;
		}
		@Override public void reportError(Exception e) {
			errCnt++;
		}
		@Override public void modelUpdated(EventObject event) {
			assertEquals(exp, errCnt);
		}
	}
	////////////////////////////////////////////////////////////
	// The actual test cases
	////////////////////////////////////////////////////////////
	
	public void testIf() {
		String cuText = 
			"class A {\n" +
			"	void foo() {\n" +
			"		if (new Object()) { }" +
			"	}\n" +
			"}\n";
		CompilationUnit cu = null;
		try {
			cu = runIt(cuText).get(0);
		} catch (ParserException e) {
			fail(e.getMessage());
		}
		try {
			new SemanticsChecker(sc).check(cu);
			fail();
		} catch (TypingException te) {
			// as expected!!
		}
	}
	
	public void testEnhancedFor() {
		String cuText =
			"class A {\n" +
			"	void foo() {\n" +
			"		for (String s: new Object[3]) {\n" +
			"		}" +
			"	}\n" +
			"}\n";
		CompilationUnit cu = null;
		try {
			cu = runIt(cuText).get(0);
		} catch (ParserException e) {
			fail(e.getMessage());
		}
		try {
			new SemanticsChecker(sc).check(cu);
			fail();
		} catch (TypingException te) {
			// as expected!!
		}
		cuText = 
			"class A {\n" +
			"	void foo() {\n" +
			"		for (String s: new String[3]) {\n" +
			"		}" +
			"	}\n" +
			"}\n";
		try {
			cu = runIt(cuText).get(0);
		} catch (ParserException e) {
			fail(e.getMessage());
		}
		new SemanticsChecker(sc).check(cu);
		cuText = 
			"class A {\n" +
			"	void foo() {\n" +
			"		for (Object o: new String[3]) {\n" +
			"		}" +
			"	}\n" +
			"}\n";
		try {
			cu = runIt(cuText).get(0);
		} catch (ParserException e) {
			fail(e.getMessage());
		}
		
		// now test collection types!
		cuText = 
			"class A {\n" +
			"	void foo() {\n" +
			"		for (String s: new java.util.ArrayList<String>()) {\n" +
			"		}" +
			"	}\n" +
			"}\n";
		try {
			cu = runIt(cuText).get(0);
		} catch (ParserException e) {
			fail(e.getMessage());
		}
		new SemanticsChecker(sc).check(cu);
		cuText = 
			"class A {\n" +
			"	static final <E> void foo(java.util.Collection<E> c) {\n"+
			"		java.util.List<E> list = new java.util.ArrayList<E>();\n"+
			"		for (E e : c) {}\n"+
			"	}\n"+
			"}\n";
		try {
			cu = runIt(cuText).get(0);
		} catch (ParserException e) {
			fail(e.getMessage());
		}
		new SemanticsChecker(sc).check(cu);
	}
}
