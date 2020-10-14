/**
 * 
 */
package recoder.testsuite.testsuite.exhaustive;

import java.util.List;

import junit.framework.TestCase;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.PropertyNames;
import recoder.java.CompilationUnit;
import recoder.service.SemanticsChecker;
import recoder.util.ProgressEvent;
import recoder.util.ProgressListener;

/**
 * @author Tobias Gutzmann
 *
 */
public class ReadJDKSources extends TestCase {

	public void testReadJDKSrc() throws ParserException {
		CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
		sc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, "/jdksrc/");
		sc.getProjectSettings().ensureSystemClassesAreInPath();
		sc.getProjectSettings().ensureExtensionClassesAreInPath();

		ProgressListener pl = new ProgressListener() {
			int x = 0;
			public void workProgressed(ProgressEvent pe) {
				if (x%50 == 0)
					System.out.print(".");
				if (++x == 3000) {
					System.out.println();
					x = 0;
				}
			}
		};

		sc.getSourceFileRepository().addProgressListener(pl);
		sc.getSourceInfo().addProgressListener(pl);

		System.out.println("Start parsing...");
		long start = System.currentTimeMillis();
		List<CompilationUnit> cus = sc.getSourceFileRepository().getAllCompilationUnitsFromPath();
		System.out.println("\nparsed " + cus.size() + " CUs in " + 
				(((System.currentTimeMillis() - start)/1000) + " seconds"));
		start = System.currentTimeMillis();
		System.out.println("Updating model...");
		start = System.currentTimeMillis();
		sc.getChangeHistory().updateModel();
		System.out.println("\nbuilt model in " + 
				(((System.currentTimeMillis() - start)/1000) + " seconds"));
		start = System.currentTimeMillis();
		for (CompilationUnit cu : cus)
			cu.validateAll();
		System.out.println("\nvalidated in " + 
				(((System.currentTimeMillis() - start)/1000) + " seconds"));
		start = System.currentTimeMillis();
        new SemanticsChecker(sc).checkAllCompilationUnits();
        System.out.println("\nsemantic checks performed in " +
        		(((System.currentTimeMillis() - start)/1000) + " seconds"));
	}
}

