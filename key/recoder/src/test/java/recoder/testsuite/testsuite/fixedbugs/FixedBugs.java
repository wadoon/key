/**
 * created on 19.10.2007
 */
package recoder.testsuite.testsuite.fixedbugs;

import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.EventObject;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelException;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.bytecode.ByteCodeParser;
import recoder.bytecode.ReflectionImport;
import recoder.convenience.CustomTreeWalker;
import recoder.convenience.TreeWalker;
import recoder.io.PropertyNames;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.JavaProgramFactory;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.modifier.Final;
import recoder.java.expression.Assignment;
import recoder.java.expression.operator.New;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.statement.LoopStatement;
import recoder.kit.MethodKit;
import recoder.kit.TypeKit;
import recoder.service.DefaultErrorHandler;
import recoder.service.ErrorHandler;
import recoder.service.SemanticsChecker;
import recoder.service.SourceInfo;

/**
 * @author Tobias Gutzmann
 *
 */
public class FixedBugs extends TestCase {
	////////////////////////////////////////////////////////////
	// helper methods / classes
	////////////////////////////////////////////////////////////
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
	// test cases
	////////////////////////////////////////////////////////////
	
	public void testConstructorStartPosition() throws ParserException {
		ServiceConfiguration sc = new CrossReferenceServiceConfiguration();
		ProgramFactory f = sc.getProgramFactory();
		CompilationUnit cu = f.parseCompilationUnit(
				"public class Test\n{\nTest s;\npublic Test(Test s)" + 
				"\n{\nthis.s = s;\n}\n}");
		sc.getChangeHistory().attached(cu);
		sc.getChangeHistory().updateModel();
		cu.validateAll();
		assertTrue(((ConstructorDeclaration)sc.getNameInfo().getClassType("Test").getConstructors().get(0)).getStartPosition().getLine() == 4);
	}
	
	/**
	 * Test for absence of a bug in PrettyPrinter that, after transformation, may 
	 * mess up single line comments.
	 * Bug reported and testcase submitted by M.Ullbrich 
	 * @throws ParserException
	 */
    public void testSingleLineCommentBug() throws ParserException {
    	ServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	ProgramFactory f = sc.getProgramFactory();
        CompilationUnit cu = f.parseCompilationUnit("class A {\n\n\n" +
                        "//some comment\r\nA a; } class B {}");
        sc.getChangeHistory().attached(cu);
        sc.getChangeHistory().updateModel();
        cu.validateAll();
        FieldDeclaration fd = (FieldDeclaration) cu.getDeclarations().get(0).getMembers().get(0);
        TypeReference oldType = fd.getTypeReference();
        TypeReference newType = TypeKit.createTypeReference(sc.getProgramFactory(), "B");
        fd.replaceChild(oldType, newType);
        sc.getChangeHistory().replaced(oldType, newType);
        sc.getChangeHistory().updateModel();
        cu.validateAll();
        String s = cu.toSource().replaceAll(" ", "");
        assertTrue(s.equals("classA{\n\n\n//somecomment\nBa;\n}classB{\n}\n"));
    }
    
    /**
     * Test for implemented generic type argument resolving in field references
     * @throws ParserException
     */
    public void testFieldTypes() throws ParserException {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        sc.getProjectSettings().ensureSystemClassesAreInPath();
        ProgramFactory f = sc.getProgramFactory();
        
        CompilationUnit cu = f.parseCompilationUnit("class B { } class G<E> { E field;   void m() { B b; b = new G<B>().field; } }");
        sc.getChangeHistory().attached(cu);
        sc.getChangeHistory().updateModel();
        cu.validateAll();

        ClassDeclaration classB = (ClassDeclaration) cu.getDeclarations().get(0);
        ClassDeclaration classG = (ClassDeclaration) cu.getDeclarations().get(1);
        MethodDeclaration methodM = (MethodDeclaration) classG.getMethods().get(0);
        Assignment assignment = (Assignment) methodM.getBody().getChildAt(1);
        Expression rhs = (Expression) assignment.getChildAt(1);
        Type rhsType = sc.getSourceInfo().getType(rhs);
        
        assertEquals(rhsType, classB);
    }
    
    public void testBasicReflectionImport() {
    	// make sure non-public fields can be read... 
    	assertTrue(ReflectionImport.getClassFile("java.lang.String") != null);
    	assertTrue(ReflectionImport.getClassFile("asdasdasd") == null);
    }
    
    public void testIncorrectFileEnd() {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	ProgramFactory f = sc.getProgramFactory();
    	String cuText = "class B { }//";
    	for (int i = 0; i < 4081; i++) {
    		cuText += " ";
    	}
    	for (int i = 4081; i < 4087; i++) {
    		// that's around the critical part, where the 
    		// size of the CU matches the JavaCCParser buffer
    		try {
        		f.parseCompilationUnit(cuText);
        		cuText += " ";
    		} catch (ParserException pe) {
    			fail();
    		}
    	}
    }
    
    public void testBug1894463() throws ParserException {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	ProgramFactory f = sc.getProgramFactory();
    	String cuText = "public class MockClass1 {\n"+
    	"public class InnerClass {"+
    	"public class InnerInnerClass { }" +
    	"}"+
    	"}"+
    	"class MockClass2 {"+
    	"void test(MockClass1 mockClass1) {"+
    	"mockClass1.new InnerClass();" +
    	"MockClass1.InnerClass ic = new InnerClass();" +
    	"ic.new InnerInnerClass();" +
    	"new InnerClass();"+
    	"}"+
    	"public class InnerClass {"+
    	"}"+
    	"}";
        CompilationUnit cu = f.parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
        sc.getChangeHistory().updateModel();
        cu.validateAll();
        ClassDeclaration mock2 = (ClassDeclaration)sc.getNameInfo().getType("MockClass2");
        StatementBlock sb = ((MethodDeclaration)mock2.getMembers().get(0)).getBody();
        assertTrue(
        		((ClassDeclaration)sc.getCrossReferenceSourceInfo().getType(
        				((New)sb.getStatementAt(0)))).getFullName().equals("MockClass1.InnerClass"));
        assertTrue(
        		((ClassDeclaration)sc.getCrossReferenceSourceInfo().getType(
        				((New)sb.getStatementAt(2)))).getFullName().equals("MockClass1.InnerClass.InnerInnerClass"));
        assertTrue(
        		((ClassDeclaration)sc.getCrossReferenceSourceInfo().getType(
        				((New)sb.getStatementAt(3)))).getFullName().equals("MockClass2.InnerClass"));
    }
    
    public void testBug1895973() throws ParserException {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        sc.getProjectSettings().ensureSystemClassesAreInPath();
    	ProgramFactory f = sc.getProgramFactory();
    	String cuText = 
    	"import java.util.ArrayList;\n"+
    	"public class MockClass extends ArrayList<String> {\n"+
    	"public String test() {\n"+
    	"// Recoder doesn't detect that 'get(0)' returns a String !\n"+
    	"return get(0).toLowerCase();\n"+
    	"}\n}\n";
    	CompilationUnit cu = f.parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    }
    
    public void testBug1911073() throws ParserException{
    	// PrettyPrinter shouldn't be messed up when statement-blocks are empty  
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        String cuText =
        	"class A {\n\tint l;\n\tvoid m() {\n\t\tswitch(l) {\n\t\t}\n\t}\n}\n";
        CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
        // check for proper indentation at end of file:
        assertTrue(cu.toSource().endsWith("        }\n    }\n}\n"));
    }
    
    public void testBug1936528() throws ParserException {
    	// find most specific method when applicable methods all have varargs  
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText =
        	"class A {\n" +
        	"void method(String s, Object... params){ }\n" +
        	"void method(String s, Throwable t, Object... params){ \n"+
        	"method(\"toto\", new Exception());}}\n";
        CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
        sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    }
    
    
    public void testBug1936842() throws ParserException {
    	// raw types and autoboxing should work together 
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText =
    	"import java.util.*;\n"+
        "class Mock\n"+
    	"{\n"+
    	"void method()\n"+
    	"{\n"+
    	"List l = new ArrayList();\n"+
    	"l.add(0);\n"+

    	"List<Object> l2 = new ArrayList<Object>();\n"+
    	"l2.add(0);\n"+
    	"}\n"+
    	"}\n";

        CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
        sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    }
    
    public void testCommentAttachment() throws ParserException {
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	String cuText = 
    		"class A {\n\tvoid m(/*c1*/ int p /*c2*/) {\n" +
    		"\t\t//Comment\n\t\tint x = /*c3*/3;\n\t}\n}\n";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    	MethodDeclaration md = (MethodDeclaration)cu.getTypeDeclarationAt(0).getMembers().get(0); 
        assertTrue(
        		md.getBody().getStatementAt(0).getComments().size() == 1);
        assertTrue(md.getParameterDeclarationAt(0).getComments().size() == 1);
        assertTrue(md.getParameterDeclarationAt(0).getVariableSpecification().getIdentifier().getComments().size() == 1);
        assertTrue(
        		((LocalVariableDeclaration)md.getBody().getStatementAt(0))
        		.getVariableSpecifications().get(0).getInitializer().getComments().size() == 1
        		);
    }
    
    public void testBug1948045() throws ParserException {
    	// parser should accept final inner classes
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	String cuText = 
    		"public class FinalInnerClass {" +
    		"public void method(){" +
    		"final class InnerClass{" +
    		"}}}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    	assertTrue(
    	((MethodDeclaration)cu.getTypeDeclarationAt(0).getMethods().get(0))
    	.getTypes().get(0).getDeclarationSpecifiers().get(0).getClass() == Final.class);
    }
    
    public void testBug1965975() throws ParserException {
    	// Endless loop when querying Methods of a parameterized Type (bytecode)
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	
    	String cuText =
    		"import java.util.List; class A { void m() { List<String> l; } }";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    	sc.getSourceInfo().getMethods((ClassType)
    	sc.getSourceInfo().getType((((LocalVariableDeclaration)
    	((MethodDeclaration)cu.getTypeDeclarationAt(0).getMethods().get(0))
    	.getBody().getStatementAt(0))).getTypeReference()));
    }
    
    public void testBug1974988() throws ParserException {
    	String declText =
    		"@Annot String decl = \"Test\";";
    	FieldDeclaration fd = JavaProgramFactory.getInstance().parseFieldDeclaration(declText);
    	fd.deepClone();
    }
    
    public void testBug1988746() throws ParserException {
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText =
    		"class A { void setDouble(Double p) {" + 
    		"Double toto = new Double(1) ;  " +
    		"Double titi = new Double(2) ;	" +
    		"this.setDouble(toto * titi);}}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    }

//    covered in java5-testsuite / EnumTest now.
//    public void testBug1988780() throws ParserException {
//    }
    
    public void testBug1996819() throws ParserException {
    	// as of java 5, return types of array types' clone()-methods
    	// have the return type
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText =
    		"class A { void m(String[] s) {" + 
    		"	s.clone(); ((Object)s).clone();}}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
        MethodReference expr = (MethodReference)
				((MethodDeclaration)cu.getTypeDeclarationAt(0).getMethods()
						.get(0)).getBody().getStatementAt(0);
        assertTrue(sc.getSourceInfo().getType(expr).getName().equals("String[]"));
        Method cloneMethod = 
        		sc.getSourceInfo().getMethod(expr);
        Type clonedType = sc.getSourceInfo().getType(cloneMethod);

        assertTrue(clonedType.getFullName().equals("java.lang.String[]"));
        // use the opportunity to check another bug:
        // array types' clone() methods overwrite java.lang.Object.clone() 
        // and do not throw (checked) exceptions ("older" java versions and java 5)
        assertTrue(cloneMethod.getExceptions().size() == 0);
        Method objCloneMethod = sc.getSourceInfo().getMethod((MethodReference)
				((MethodDeclaration)cu.getTypeDeclarationAt(0).getMethods().get(0)).getBody().getStatementAt(1));
        assertTrue(objCloneMethod != cloneMethod);
        assertTrue(MethodKit.getAllRedefinedMethods(cloneMethod).contains(objCloneMethod));
        // TODO 0.90 check the below check...
//        assertTrue(MethodKit.getRedefiningMethods(sc.getCrossReferenceSourceInfo(), objCloneMethod).contains(cloneMethod));
    }
    
    public void testBug2020825() throws ParserException {
    	// inner types don't "inherit" type parameters of outer classes
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	// this should be valid code:
    	String cuText =
    		"import java.util.*; class A<E> { class B extends ArrayList<E> {} B m() { new A<String>().m().get(0).toLowerCase(); return null; }}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    }
    
    public void testBug2013315() throws ParserException {
    	// generic fields in bytecode
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	// this is the source code of Test.class:
		//import java.util.*;
    	//public class Test
		//{
		//public Map<String, Number> myMap = new HashMap<String, Number>() ;
		//}

    	sc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, "test/fixedBugs/Bug2013315");
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText =
    		"class X {{Test instance = new Test();"+
    		"instance.myMap.get(\"\").shortValue(); }}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
    }
    
    public void testBug2044230() throws ParserException {
    	// this should parse...
    	String cuText =
    		"class A { public static final double MAX_VALUE = 0x1.fffffffffffffP+1023;}";
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProgramFactory().parseCompilationUnit(cuText);
    }
    
    public void testBug2045181() throws ParserException {
    	// on demand imports don't find imported types
    	String cuText =
    		"package B; class A { static class InA {}}";
    	String cu2Text =
    		"package B;"+
    		"import B.A.*;"+
    		"class B extends InA {}";
       	runIt(cuText, cu2Text);
    }
    
    public void testBug2045207() throws ParserException {
    	// type parameters not supported for constructor declarations
    	// this should compile:
    	String cuText =
    		"class A {public <T> A(T p1, Class<T> p2) { }}";
       	runIt(cuText);
    }
    
    public void testBug2045354 () throws ParserException {
    	// this should be valid code, but cu.validateAll() fails currently:
    	String cuText =
    		"import java.security.*;" +
    		"class A implements PrivilegedAction<String> {" +
    		"public String run() {" +
    		"	return null;" +
    		"}" +
    		"{ A a = new A(); String s; s = AccessController.doPrivileged(a); }" +
    		"}";
       	runIt(cuText);
    }
    
    public void testBug2046005() throws ParserException {
    	// the code below should be valid
    	// this is actually not bug 2046005, but highly related.
    	// note the <?> in Constructor<?> constr
    	// which makes the code valid. In the initial bugreport at sf.net,
    	// <?> was not present, making the code invalid (but still compilable with javac).
    	// we use this method now to fix the related bug...
    	// TODO requires JDK 1.6 ...
    	String cuText =
    		"import java.lang.reflect.Constructor;"+
    		"import java.beans.ConstructorProperties;"+
    		"class A {"+
    		"{"+
    		"final Class<ConstructorProperties> propertyNamesClass = ConstructorProperties.class;"+
    		"Constructor<?> constr = null;"+
    		"constr.getAnnotation(propertyNamesClass).value();"+
    		"}"+
    		"}";
    	runIt(cuText);
    }
    
    public void testBug2046167() throws ParserException {
    	// TODO should be rewritten to not use com.sun...
    	String cuText = 
    		"package com.sun.org.apache.xerces.internal.impl.xs.identity;"+
    		"import com.sun.org.apache.xerces.internal.impl.xpath.XPathException;"+
    		"import com.sun.org.apache.xerces.internal.util.SymbolTable;"+
    		"import com.sun.org.apache.xerces.internal.xni.NamespaceContext;"+
    		"public class Field {"+
    		"public static class XPath"+
    		"    extends com.sun.org.apache.xerces.internal.impl.xpath.XPath {"+
    		"    public XPath() throws XPathException {"+
    		"        super(null, null, null);"+
    		"        com.sun.org.apache.xerces.internal.impl.xpath.XPath.Axis axis = null;"+
    		"        if (axis.type == XPath.Axis.ATTRIBUTE) {"+
    		"               throw new XPathException(null);"+
    		"        }"+
    		"    }"+
    		"}"+
    		"}";
    	runIt(cuText);
    }

    public void testBug2046337() throws ParserException {
    	String cuText = "class A { void foo() {new String[3].getClass();}}";
    	CompilationUnit cus = runIt(cuText).get(0);
    	getClass();
    	ClassType t = (ClassType)cus.getFactory().getServiceConfiguration().getSourceInfo().getType(
    	((MethodDeclaration)cus.getTypeDeclarationAt(0).getMembers().get(0))
    	.getBody().getStatementAt(0));
    	assertTrue(t.getFullSignature().equals("java.lang.Class<? extends java.lang.String[]>"));
    }
    public void testExplicitGenInvokeParserTest() throws ParserException {
    	String cuText = "class A{{java.util.Collections.<String, String[]>emptyMap();}}";
    	runIt(cuText);
    }
    
    public void testCaptureOfIssue() throws ParserException {
    	// unreported, as in development version only. Issue 
    	// when passing "capture-of types" as arguments. 
    	String cuText = "class A {" +
    			"void foo(Number n) { }" +
    			"void bar() {" +
    			"  java.util.Iterator<? extends Number> it = null;" +
    			"  foo(it.next());" +
    			"}" +
    			"}";
    	runIt(cuText);
    }
    
    
    public void testEnumSupertypeBug() throws ParserException {
    	String cuText = "enum A implements java.util.Comparator<Number> {" +
    			"; { Number[] n = null; java.util.Arrays.sort(n, this); }}";
    	runIt(cuText);
    }
    
    public void testCaptureBugParamMatches() throws ParserException {
    	// unfiled bug, DefaultProgramModelInfo.paramMatches() had a problem.
    	String cuText = 
    		"import java.util.Comparator;"+
    		"class A {"+
    		"private static <T> void binarySearch0(T[] a, T key, Comparator<? super T> c) {"+
    		"	    c.compare(key, key);"+
    		"}"+
    		"}";
    	runIt(cuText);
    }
    
    public void testClassLiteralTypes() throws ParserException {
    	// correct types for class literals? related to bug 2046337
    	String cuText =
    		"class A {" +
    		"void m() {" +
    		"void.class.cast(null);" +
    		"int.class.cast(null);" +
    		"Integer.class.cast(null);}}";
    	CompilationUnit cu = runIt(cuText).get(0);
    	StatementBlock sb = ((MethodDeclaration)cu.getTypeDeclarationAt(0).getMembers().get(0)).getBody();
    	SourceInfo si = cu.getFactory().getServiceConfiguration().getSourceInfo();
    	assertTrue(((ClassType)si.getType(sb.getStatementAt(0))).getFullSignature().equals("java.lang.Void"));
    	assertTrue(((ClassType)si.getType(sb.getStatementAt(1))).getFullSignature().equals("java.lang.Integer"));
    	assertTrue(((ClassType)si.getType(sb.getStatementAt(2))).getFullSignature().equals("java.lang.Integer"));
    }
    
    public void testValidateBug() throws ParserException {
    	// unfiled validate()-bug. Code below is valid but wasn't in
    	// intermediate development version
    	String cuText =
    		"class A { {byte b; b = 5; " +
    		"Class<?> classes[]; classes = new Class[20];" +
    		"}}";
    	runIt(cuText);
    }
    
    public void testTypeInferenceBug() throws ParserException {
    	// unfiled. Type inference issue.
    	String cuText =
    		"import java.util.Collection;"+
    		"class A { " +
    		"static class B<E> {"+
    		"E bar[];"+
    		"}" +
    		"static class C<E> extends B<E> {" +
    		"public void foo(Collection<? extends E> c) {"+
    		"      E[] a = null;"+
    		"      a = c.toArray(bar);" +
    		"}"+
    		"	}"+
    		"}";
    	runIt(cuText);
    }
    
    public void testAnonymousEnumInstanceParent() throws ParserException {
    	// unfiled. Recoder didn't properly return 
    	// the supertypes of an anonymous enum class body.
    	String cuText = "public enum A {"+
    		  "CONST { public int foo() { return 0; }};"+
    		  "public int foo() { return -1; }"+
    		  "}"+

    		  "class B {"+
    	      "void foo(A a) { foo(A.CONST); }"+
    		  "}";
    	runIt(cuText);
    }
    
    public void testValidateBug2() throws ParserException {
    	// another unfiled validate() bug
    	String cuText = "public class A<E> extends java.util.AbstractQueue<E> {"+
    	"private final Object lock;"+
    	"private class B {"+
    	"public void foo() { final Object i = A.this.lock; }"+
    	"}}";
    	runIt(cuText);
    }
    
    public void testBug2044375() throws ParserException {
    	// should report an error, not throw an exception. 
    	String cuText =
    		"import java.util.HashMap;" +
    		"class A {" +
    		"  HashMap<String, Unknown<String, String>> field;" +
    		"  public Unknown<String, String> getChangeString(String s) {" +
    		"    return field.get(s);" +
    		"  }" +
    		"}";
    	try {
    		runIt(new SilentErrorHandler(2), cuText);
    	} catch (ModelException me) {
    		// okej, we expect this!
    	}
    }
    
	public void testEnumValueOfReturnType() throws ParserException {
    	// unfiled
    	String cuText = "public class A { void foo() { " +
    			"Class c = null; Enum.valueOf(c, \"WAITING\"); }}";
    	CompilationUnit cu = runIt(cuText).get(0);
    	SourceInfo si = cu.getFactory().getServiceConfiguration().getSourceInfo();
    	Type t = si.getType(((MethodDeclaration)cu.getTypeDeclarationAt(0).getMembers().get(0))
    			.getBody().getStatementAt(1));
    	assertTrue(t.getFullName().equals("java.lang.Enum")); // leftmost bound
    }
    
    public void testArraySupertypes() {
		CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
       	sc.getProjectSettings().ensureSystemClassesAreInPath();
       	ClassType ct = sc.getNameInfo().getClassType("java.lang.String[]");
       	Set<String> supStr = new HashSet<String>();
       	for (ClassType sup : ct.getSupertypes())
       		supStr.add(sup.getFullSignature());
       	assertTrue(supStr.size() == 4);
       	assertTrue(supStr.contains("java.lang.Object[]"));
       	assertTrue(supStr.contains("java.io.Serializable[]"));
       	assertTrue(supStr.contains("java.lang.Comparable<java.lang.String>[]"));
       	assertTrue(supStr.contains("java.lang.CharSequence[]"));
    }

    
    public void testRHSUnboxing() throws ParserException {
    	// unreported bug: instead of boxing LHS, unbox RHS of an assignment.
    	String cuText = 
    		"class A { {" +
    		"float num = 0;" +
    		"int i = 0;" +
    		"int[] args = null;"+
    	"	i++;"+
    	"	num = Integer.valueOf(args[i]);"+
    	"}"+
    	"}";
    	CompilationUnit cu = runIt(cuText).get(0);
    	cu.validateAll();
    }
    
    public void testBug2071287() throws ParserException {
    	// scoping after transformation
    	String cuText =
    		"class A {\n" +
    		"void m() {\n" +
    		"  {\n" +
    		"    for (;;) {\n" +
    		"      int n;\n" +
    		"    }\n" +
    		"  }\n" +
    		"  int n;\n" +
    		"}\n" +
    		"}\n";
    	List<CompilationUnit> cul = runIt(cuText);
    	for (CompilationUnit cu : cul)
    		cu.validateAll();
    	
    	TreeWalker tw = new TreeWalker(cul.get(0));
    	while (tw.next(LoopStatement.class)) {
    		LoopStatement ls = ((LoopStatement)tw.getProgramElement());
    		LoopStatement repl = ls.deepClone();
    		ls.getASTParent().replaceChild(ls, repl);
    		sc.getChangeHistory().replaced(ls, repl);
    	}
    	sc.getChangeHistory().updateModel();
    }
    
    public void testBytecodeInnerClass() throws ParserException {
    	runIt(); // dummy setup-call
    	// need to query the outer type first, in order to avoid a bug:
    	sc.getNameInfo().getClassType("java.util.AbstractList");
    	ClassType itr = sc.getNameInfo().getClassType("java.util.AbstractList.Itr");
    	assertTrue(itr.isInner());
    }
    
    public void testBug2088980() throws ParserException {
    	// actually, a duplicate of bug 2000780. But we don't have an explicit
    	// testcase for that one.
    	String cuText = 
    			"import java.util.*;" +
    			"class A {" +
    			"	public <T> T methodCallingGenericMethod(T bean) {"+
    			"		Collection<T> aList = new ArrayList<T>();"+
    			"		aList.add(Collections.singletonList(bean).get(0));"+
    			"	}" +
    			"}";
    	List<CompilationUnit> cus = runIt(cuText);
    	for (CompilationUnit cu : cus)
    		cu.validateAll();
    }
    
    public void testBug2132665() throws ParserException {
    	// anonymous class with following call to a newly declared method
    	String cuText =
    		"import java.awt.Dialog;"+
    		"import java.awt.Frame;"+

    		"public class Main {"+
    		"public static void main(String[] args) {"+
    		"Frame frame = new Frame();"+

    		"new Dialog(frame){"+
    		"public void init(){"+
    		"//initme\n"+
    		"}"+
    		"}.init();"+
    		"}"+
    		"}";
    	List<CompilationUnit> cus = runIt(cuText);
    	for (CompilationUnit cu : cus)
    		cu.validateAll();
    	// the following is some experimental testing. Reported via email
    	// to me, but I don't think it's a bug (getName() == null should
    	// be desired behavior!?)
    	CustomTreeWalker ctw = new CustomTreeWalker(cus.get(0));
    	ctw.next(MethodDeclaration.class);
    	ctw.next(MethodDeclaration.class);
    	MethodDeclaration method = (MethodDeclaration)ctw.getProgramElement();
        assertNotNull(method.getContainingClassType().getFullName());
        // TODO think about this
//        System.out.println(method.getContainingClassType().getName()); 
    }
    
    public void testBug2134267() throws ParserException {
    	// problem resolving package names from bytecode classes when naming conventions are not follow (e.g., COM.xyz)
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, "test/fixedBugs/Bug2134267/*.jar");
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText = 
    		"package runner;"+
    		"public class Main {"+
    		"public static void main(String[] args) {"+
    		"COM.AClass value = null;"+
    		"}"+
    		"}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
   		cu.validateAll();
    }
    
    public void testBug2155226() throws ParserException {
    	// this should report a ModelException, not throw an UnsupportedOperationException
    	String cuText =
       		"class KnownBasicClass"+
       		"{}"+

       		"class TestFailed1 extends UnknownGenericClass<KnownBasicClass>{"+
       		"}";
       	try {
    		runIt(new SilentErrorHandler(1), cuText);
    	} catch (ModelException me) {
    		// ok, we expect this!
    	}
    }
    
    public void testBug2230018() throws ParserException {
    	// should again report a ModelException, not throw an Exception...
    	String cuText =
    		"import com.pkg.UnknownClass;"+
    		"class KnownBasicClass"+
    		"{"+
    		"    int nb = UnknownClass.CONSTANT;"+
    		"}"	;
    	runIt(new SilentErrorHandler(4), cuText); 
    }

    public void testBug2230018_2() throws ParserException {
    	// should again report a ModelException, not throw an Exception...
    	// DO NOT MERGE WITH testBug2230018(), OTHERWISE THIS BUG WON'T BE DETECTED DUE TO CACHING ISSUES! 
    	String cuText = 
    		"package com.example.generics;"+
    		"import com.Blubb;"+
    		"public class ExtendsUnknownGeneric extends Toto<DynamicType>"+
    		"{"+ 
    		"  public void method()"+
    		"  {"+
    		"    String s = Blubb.CONSTANTE ;"+
    		"  }"+
    		"}";
    	runIt(new SilentErrorHandler(6), cuText); 
    }

    public void testOverwritingWithPrimitives() throws ParserException {
    	// Never been a bug, and never should be, so we add this here: 
    	// don't use autoboxing for determining overwriting methods ;-)
    	String cuText =
    		"abstract class A<T> { abstract void foo(T a); }\n"+
    		"class B extends A<Integer> {\n"+ 
    		"	void foo(int a) {}\n"+
    		"}\n"+
    		"class C extends B {" +
    		"	void foo(long a) {" +
    		"	}\n" +
    		"}";
    	List<CompilationUnit> cus = runIt(cuText);
    	for (CompilationUnit cu: cus)
    		cu.validate();
    	new SemanticsChecker(sc).checkAllCompilationUnits();
    	assertEquals(MethodKit.getRedefinedMethods(
    			cus.get(0).getTypeDeclarationAt(1).getMethods().get(0)).size(), 0);
    	assertEquals(sc.getSourceInfo().getAllMethods(cus.get(0).getTypeDeclarationAt(1)).size(), 13);
    	assertEquals(MethodKit.getRedefinedMethods(
    			cus.get(0).getTypeDeclarationAt(2).getMethods().get(0)).size(), 0);
    	assertEquals(sc.getSourceInfo().getAllMethods(cus.get(0).getTypeDeclarationAt(2)).size(), 14);
    }
    public void testCrossReferencer() throws ParserException {
    	// Never been a bug, and never should be. I just suspected it once, 
    	// and now that it's written, it stays for the sake of testing :-P
    	String cuText =
    		"class A {\n"+
    		"	void foo(long a) {" +
    		"		java.util.LinkedList ll = new java.util.LinkedList();\n" +
    		"	}" +
    		"}";
    	List<CompilationUnit> cus = runIt(cuText);
    	for (CompilationUnit cu: cus)
    		cu.validate();
    	new SemanticsChecker(sc).checkAllCompilationUnits();
    	assertEquals(sc.getCrossReferenceSourceInfo().getReferences(
    			sc.getNameInfo().getType("java.util.LinkedList")).size(), 2);
    }

    
    public void testBug2343547() throws Exception {
    	new ByteCodeParser().parseClassFile(new FileInputStream("test/fixedBugs/Bug2343547/ICacheManager.class"));
    }

}
