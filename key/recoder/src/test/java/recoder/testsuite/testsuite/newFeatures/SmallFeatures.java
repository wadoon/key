package recoder.testsuite.testsuite.newFeatures;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.java.CompilationUnit;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.TypeReference;
import recoder.service.ErrorHandler;
import recoder.service.SemanticsChecker;
import junit.framework.TestCase;

public class SmallFeatures extends TestCase {
	// evil... cloned code !!!
	private CrossReferenceServiceConfiguration sc;
	private List<CompilationUnit> runIt(String ... cuTexts) throws ParserException {
		return runIt(null, cuTexts);
	}

	private List<CompilationUnit> runIt(ErrorHandler eh, String ... cuTexts) throws ParserException {
		sc = new CrossReferenceServiceConfiguration();
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
       	new SemanticsChecker(sc).checkAllCompilationUnits();
        return cus;
	}

	
	public void testCrossReferenceIssues() throws ParserException {
    	String cuText = 
    		"class A<T> {\n" +
    		"	A<java.util.List> f1;\n" +
    		"	A[] f2;\n" +
    		"	A<java.util.List> f3;\n" +
    		"}";
    	List<CompilationUnit> cus = runIt(cuText);
    	TypeDeclaration typeA = cus.get(0).getTypeDeclarationAt(0);
    	List<TypeReference> trs = sc.getCrossReferenceSourceInfo().getReferences(typeA);
    	assertEquals(2, trs.size());
    	trs = sc.getCrossReferenceSourceInfo().getReferences(typeA, true);
    	assertEquals(3, trs.size());
    	trs = sc.getCrossReferenceSourceInfo().getReferences(typeA, false);
    	assertEquals(2, trs.size());
    	trs = sc.getCrossReferenceSourceInfo().getReferences(sc.getNameInfo().getClassType("java.util.List"));
    	assertEquals(2, trs.size());
    }
}
