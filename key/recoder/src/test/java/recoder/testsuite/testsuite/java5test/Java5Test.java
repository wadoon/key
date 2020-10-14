package recoder.testsuite.testsuite.java5test;

import java.io.File;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.EventObject;
import java.util.List;

import junit.framework.TestCase;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.abstraction.AnnotationUse;
import recoder.abstraction.ClassType;
import recoder.abstraction.Constructor;
import recoder.abstraction.Field;
import recoder.abstraction.Method;
import recoder.abstraction.Package;
import recoder.abstraction.ParameterizedType;
import recoder.abstraction.ProgramModelElement;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.bytecode.AnnotationUseInfo;
import recoder.bytecode.MethodInfo;
import recoder.convenience.ForestWalker;
import recoder.convenience.Format;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.io.PropertyNames;
import recoder.io.SourceFileRepository;
import recoder.java.Comment;
import recoder.java.CompilationUnit;
import recoder.java.Declaration;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.EnumConstantSpecification;
import recoder.java.declaration.EnumDeclaration;
import recoder.java.declaration.FieldSpecification;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.VariableReference;
import recoder.kit.MiscKit;
import recoder.kit.transformation.java5to4.EnhancedFor2For;
import recoder.kit.transformation.java5to4.MakeConditionalCompatible;
import recoder.kit.transformation.java5to4.RemoveAnnotations;
import recoder.kit.transformation.java5to4.RemoveCoVariantReturnTypes;
import recoder.kit.transformation.java5to4.RemoveStaticImports;
import recoder.kit.transformation.java5to4.ReplaceEnums;
import recoder.kit.transformation.java5to4.ResolveBoxing;
import recoder.kit.transformation.java5to4.ResolveGenerics;
import recoder.kit.transformation.java5to4.ResolveVarArgs;
import recoder.kit.transformation.java5to4.methodRepl.ApplyRetrotranslatorLibs;
import recoder.kit.transformation.java5to4.methodRepl.ReplaceEmptyCollections;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.service.AmbiguousStaticFieldImportException;
import recoder.service.ErrorHandler;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;
import recoder.service.UnresolvedReferenceException;
import recoder.service.ConstantEvaluator.EvaluationResult;
import recoder.util.Debug;
import recoder.util.HashCode;
import recoder.util.Index;
import recoder.util.Order;
import recoder.util.Sorting;

/*
 * Created on 11.03.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 */

/**
 * @author gutzmann
 *
 */
public class Java5Test extends TestCase {
    private CrossReferenceServiceConfiguration crsc;
    private SourceFileRepository dsfr;
    private boolean silent = true;
    
    private void setPath(String base) {
        crsc = new CrossReferenceServiceConfiguration();
        dsfr = crsc.getSourceFileRepository();
        crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, 
				new File("test/java5/src/" + base + "/").getAbsolutePath() +
				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jce.jar" + 
				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jsse.jar " +
				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "rt.jar"  +
				File.pathSeparatorChar + "test/java5/src/prettyprinting/testcode/java/lib/namensfehler.jar"
        );
        crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH,
                new File("test/java5/output/" + base + "/").getAbsolutePath());
        crsc.getProjectSettings().ensureExtensionClassesAreInPath();
        crsc.getProjectSettings().ensureSystemClassesAreInPath();
    }
    
    private void runIt() {
//        boolean b = crsc.getProjectSettings().java5Allowed();
        crsc.getProjectSettings().setProperty(PropertyNames.JAVA_5, "true");
        crsc.getProjectSettings().setProperty(PropertyNames.TABSIZE, "4");
        try {
            dsfr.getAllCompilationUnitsFromPath();
            crsc.getChangeHistory().updateModel();
        } catch (ParserException pe) {
            System.err.println(pe.getMessage());
            fail("unexpected ParserException");
//        } finally {
//            crsc.getProjectSettings().setProperty(ProjectSettings.Java_5, Boolean.toString(b));
        }
        List<CompilationUnit> cul = dsfr.getCompilationUnits();
        for (int i = 0; i < cul.size(); i++) {
        	cul.get(i).validateAll();
        }
    }
    
    private void writeBack() {
        try {
            dsfr.printAll(true);
        } catch (IOException e) {
            fail();
        }
    }
 
    public void testTransformations() {
    	setPath("transformations");

    	runIt();
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	
    	ApplyRetrotranslatorLibs rt = new ApplyRetrotranslatorLibs(crsc);
    	rt.execute();
    	// TODO remove !!!
    	System.out.println("QUITTING EARLY !!!!");
    	if (true)
    		return;
    	
    	MakeConditionalCompatible mcc = new MakeConditionalCompatible(crsc, cul);
    	mcc.execute();
    	
    	EnhancedFor2For eff = new EnhancedFor2For(crsc, cul);
    	eff.execute();
    	
    	ResolveGenerics rg = new ResolveGenerics(crsc, cul);
    	rg.execute();
    	
    	RemoveCoVariantReturnTypes rc = new RemoveCoVariantReturnTypes(crsc, cul);
    	rc.execute();
    	
    	RemoveAnnotations ra = new RemoveAnnotations(crsc, cul);
    	ra.execute();
    	
    	RemoveStaticImports rsi = new RemoveStaticImports(crsc, cul);
    	rsi.execute();
    	
    	ResolveBoxing rb = new ResolveBoxing(crsc, cul);
    	rb.execute();
    	
    	ResolveVarArgs rva = new ResolveVarArgs(crsc, cul);
    	rva.execute();
    	
    	ReplaceEnums re = new ReplaceEnums(crsc, cul);
    	re.execute();
    	
    	ReplaceEmptyCollections rec = new ReplaceEmptyCollections(crsc);
    	rec.execute();
    	
    	writeBack();
    }
    
    public void testComments() {
    	setPath("comments");
    	runIt();
    	
    	ForestWalker fw = new ForestWalker(dsfr.getCompilationUnits());
    	while (fw.next()) {
    		ProgramElement pe = fw.getProgramElement();
    		List<Comment> cl = pe.getComments();
    		if (cl != null) {
    			for (int i = 0; i < cl.size(); i++) {
    				Comment c = cl.get(i);
    				String name = pe.getClass().getSimpleName();
    				if (c.getText().indexOf(name) == -1) {
    					//System.err.println(pe.getClass().getName() + " - " + c.getText());
    				}
    			}
    		}
    	}
    	
    	reparseAndCompare("comments");
    }
    
//    public void testReadJava5Sources() {
//    	setPath("jdk5_src");
//    	
//        ErrorHandler defaultErrorHandler = crsc.getProjectSettings().getErrorHandler();
//        defaultErrorHandler.setErrorThreshold(9999);
//        runIt();
//        
//        //reparseAndCompare("jdk5_src");
//    }
    
    public void testAmbiguities() {
        setPath("errortest");
        final ErrorHandler defaultErrorHandler = crsc.getProjectSettings().getErrorHandler();
        defaultErrorHandler.setErrorThreshold(9999);
        crsc.getProjectSettings().setErrorHandler(new ErrorHandler() {
            private int errNum = 0; 
            public int getErrorThreshold() {
                return 9999;
            }
            public void setErrorThreshold(int maxCount) { Debug.assertBoolean(false); }
            public void modelUpdating(EventObject event) { /* ignore */ }
            public void modelUpdated(EventObject event) { assertTrue("Not enough errors, only " + errNum, errNum == 10); }

            public void reportError(Exception e) throws RuntimeException {
                switch (errNum++) {
                	case 0: assertTrue(e instanceof AmbiguousStaticFieldImportException);
                		    break;
                	case 1: 
                	case 2:
                	case 3:
                	case 4:
                	case 5:
                	case 6:
                	case 7:
                	case 8:
                	case 9:
                	    	assertTrue(e instanceof UnresolvedReferenceException);
                	    	break;
                	default: 
                	    	System.err.println("failing:\n" + "    " + e.getMessage());
                	    	fail("Too many errors");
                }
                if (!silent) {
                    System.out.print("ok: ");
                	// taken from DefaultErrorHandler and slightly modified
                	String className = e.getClass().getName();
                	className = className.substring(className.lastIndexOf('.') + 1);
                	System.out.println("*** " + errNum + ": " + className);
                	System.out.println("    " + e.getMessage());
                	System.out.println();
                	// end of 'taken from DefaultErrorHandler'
                }
            }
        });

        runIt();

        //reparseAndCompare("errortest"); would cause too many errors
    }
    
    private String getAnnotationName(AnnotationUse au) {
    	if (au instanceof AnnotationUseInfo) {
    		AnnotationUseInfo aus = (AnnotationUseInfo)au;
    		return dsfr.getServiceConfiguration().getByteCodeInfo().getAnnotationType(aus).getFullName();
    	} else {
    		AnnotationUseSpecification aus = (AnnotationUseSpecification)au;
    		return dsfr.getServiceConfiguration().getSourceInfo().getAnnotationType(aus).getFullName();
    	}
    }
   
    public void testAnnotations() {
        setPath("annotationtest");
        runIt();
        // test source code annotation support
        NameInfo ni = dsfr.getServiceConfiguration().getNameInfo(); 
        Package p = ni.getPackage("annotationtest");
        List<? extends AnnotationUse> ann = p.getPackageAnnotations();
        assertTrue(ann.size() == 1);
        assertTrue(getAnnotationName(ann.get(0)).equals("annotationtest.Annot"));
        
        p = ni.getPackage("a");
        ann = p.getPackageAnnotations();
        assertTrue(ann.size() == 1);
        assertTrue(getAnnotationName(ann.get(0)).equals("a.B"));
        assertTrue(ni.getType("annotationtest.package-info") == null);
        assertTrue(ni.getType("a.package-info") == null);
        
        // test bytecode annotation support
        ClassType ct = ni.getClassType("java.lang.annotation.Retention");
        assertTrue(ct != null);
        assertTrue(ct.isAnnotationType());
        assertTrue(ct.getAllSupertypes().size() == 3);
        
        ct = ni.getClassType("a.C");
        List<? extends Method> ml = ct.getMethods();
        StringBuilder output = new StringBuilder();
        for (int i = 0, s = ml.size(); i < s; i++) {
        	MethodInfo m = (MethodInfo)ml.get(i);
        	String param[] = m.getParameterTypeNames();
        	
        	output.append(m.getName() + "(");
        	boolean first = true;
        	for (int j = 0; j < param.length; j++) {
        		if (!first) 
        			output.append(",");
        		first = false;
        		AnnotationUseInfo annot[] = m.getAnnotationsForParam(j);
        		for (int k = 0; k < annot.length; k++) {
        			output.append(annot[k] + " ");
        		}
        		output.append(param[j]);
        	}
        	output.append(")");
        }
        assertEquals(output.toString(),
        		"foo(@a.BC int)"+
        		"bar(@a.BC int,@a.CD @a.BC int,@a.BC @a.CD int)"+
        		"bar2(@a.BC int,int)");
        // 11 methods from Object + 1 from Annotation:
        assertTrue(ni.getClassType("a.BC").getAllMethods().size() == 12);
        
        reparseAndCompare("annotationtest");
    }
    
    public void testEnums() {
    	setPath("enumtest");
    	runIt();
    	NameInfo ni = dsfr.getServiceConfiguration().getNameInfo();
    	EnumDeclaration etd = (EnumDeclaration)ni.getType("enumtest.Color");
    	Constructor c = etd.getConstructors().get(0);
    	List<ConstructorReference> crl = crsc.getCrossReferenceSourceInfo().getReferences(c);
    	assertTrue(crl.size() == 3);
    	
    	EnumConstantSpecification ecd = (EnumConstantSpecification)ni.getField("enumtest.jls.Operation.PLUS");
    	Method m = ecd.getConstructorReference().getClassDeclaration().getMethods().get(0);
    	int s = crsc.getCrossReferenceSourceInfo().getReferences(m).size();
    	assertTrue(s == 1);
    	reparseAndCompare("enumtest");
    }
    
    public void testGenerics() {
    	setPath("generictest");
    	runIt();
    	crsc.getNameInfo().getType("a.BytecodeGenerics");
    	
    	NameInfo ni = dsfr.getServiceConfiguration().getNameInfo();
    	TypeDeclaration td = (TypeDeclaration)ni.getType("generictest.D");
    	for(int i = 0; i < td.getMethods().size(); i++) {
        	Method m = td.getMethods().get(i);
        	if (m.getName().equals("foobar")) {
        		MethodDeclaration md = (MethodDeclaration)m;
        		assertTrue("List<List<Map<String, List<String>>>>".equals(md.getTypeReference().toSource().trim()));
//        		TreeWalker tw = new TreeWalker(md);
//        		while (tw.next()) {
//        			ProgramElement pe = tw.getProgramElement();
//        			System.out.println(pe.getClass().getName() + " " + pe.getStartPosition());
//        		}
        	}
    	}
//    	System.err.println(td.toSource());
    	reparseAndCompare("generictest");
    }

	private void reparseAndCompare(String path) {
		try {
    		StringWriter oldReport = new StringWriter(10000);
			createExtendedReport(oldReport);
			scrubOutputPath("test/java5/output/" + path + "/");
			writeBack();
			setPath("../output/" + path + "/");
			runIt();
			StringWriter newReport = new StringWriter(10000);
			createExtendedReport(newReport);
			StringBuffer oldBuf = oldReport.getBuffer();
			StringBuffer newBuf = newReport.getBuffer();
			//assertTrue(oldBuf.length() == newBuf.length());
			
			for (int i = 0, rep = 5; i < Math.min(oldBuf.length(), newBuf.length()) && rep > 0; i++) {
				if (oldBuf.charAt(i) != newBuf.charAt(i)) {
					if (i > 1 && oldBuf.charAt(i-1) == '.') {
						// may be an anonymous class: skip till next '.', but at most 10(?) digits.
						// TODO deal with numbers of different length...
						int j = i+1;
						while (Character.isDigit(oldBuf.charAt(j)) && Character.isDigit(newBuf.charAt(j))
								&& j < i+10)
							j++;
						if (j - i > 6)
							i = j;
						continue;
					}
//					System.err.println(i);
//					System.err.println(oldBuf.substring(i-10, i+10));
//					System.err.println(newBuf.substring(i-10, i+10));
//					System.err.println();
					rep--;
				}
			}
		} catch (IOException e) {
			fail();
		}
	}
	
	private void scrubOutputPath(String path) {
		File myPath = new File(path);
		File list[] = myPath.listFiles();
		if (list==null) return;
		for (int i = 0; i < list.length; i++) {
			File current = list[i];
			if (current.isDirectory()) {
				scrubOutputPath(current.getAbsolutePath());
				current.delete(); // if possible...
			} 
			else if (current.isFile() && current.getName().endsWith(".java")) current.delete();
		}
	}
    
    public void testPrettyPrinter() {
    	setPath("prettyprinting");
    	runIt();
        ClassDeclaration cd = (ClassDeclaration)crsc.getNameInfo().getClassType("A");
        List<? extends Field> fl = cd.getFields();
        ASTList<Comment> cml = new ASTArrayList<Comment>(1);
        cml.add(new Comment("/*comment to field spec 'a'*/", true));
        ((FieldSpecification)fl.get(0)).setComments(cml);
        MiscKit.unindent((FieldSpecification)fl.get(0));
//        System.err.println(((FieldSpecification)fl.getField(0)).toSource());
//        System.err.println(cd.getMembers().getMemberDeclaration(0).toSource());
//        System.err.println(cd.getMembers().getMemberDeclaration(1).toSource());
//        System.err.println(((FieldSpecification)fl.getField(1)).toSource());
//        
//        //System.err.println()
//        
//        for (int i = 0; i < crsc.getCrossReferenceSourceInfo().getReferences(crsc.getNameInfo().getClassType("listexample.NTuple").getConstructors().getConstructor(0)).size(); i++) {
//        	ConstructorReference cr = crsc.getCrossReferenceSourceInfo().getReferences(crsc.getNameInfo().getClassType("listexample.NTuple").getConstructors().getConstructor(0)).getConstructorReference(i); 		
//        	System.err.println(cr.toSource());
//        }
        
        reparseAndCompare("prettyprinting");
    }
    
    public void testParameterizedTypes() throws ParserException {
    	// TODO this test doesn't really test so much right now...
    	CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
    	sc.getProjectSettings().ensureSystemClassesAreInPath();
    	String cuText =
    		"class A<T> { T foo(String dummy, T param) throws T { new A<String>(); return null; }}";
    	CompilationUnit cu = sc.getProgramFactory().parseCompilationUnit(cuText);
    	sc.getChangeHistory().attached(cu);
    	sc.getChangeHistory().updateModel();
        cu.validateAll();
        
        Type t = sc.getSourceInfo().getType(
        ((MethodDeclaration)cu.getTypeDeclarationAt(0).getMembers().get(0)).getBody().getStatementAt(0));
        assertTrue(t instanceof ParameterizedType);
//        ParameterizedType pt = (ParameterizedType)t;
//        for (Method m :  pt.getAllMethods()) {
//        	System.out.println(m.getReturnType() != null ? m.getReturnType().getFullName() : "void");
//        	for (Type param : m.getSignature()) {
//        		System.out.println("\t\t" + param.getFullName());
//        	}
//        	if (m.getExceptions() != null) {
//        		for (Type exc : m.getExceptions()) {
//        			System.out.println("\t\t" + exc.getFullName());
//        		}
//        	} else {
//        		System.out.println("\t\t(No exceptions)");
//        	}
//        }
    }

    final static Order UNIT_NAME_ORDER = new Order.CustomLexicalOrder() {
        protected String toString(Object x) {
            return Naming.toCanonicalName((CompilationUnit) x);
        }
    };
    
    protected void createExtendedReport(Writer out) throws IOException {
    	List<CompilationUnit> units = crsc.getSourceFileRepository().getCompilationUnits();
        // sort by name
        CompilationUnit[] uarray = new CompilationUnit[units.size()];
        for (int i = 0; i < uarray.length; i++) {
            uarray[i] = units.get(i);
        }
        Sorting.heapSort(uarray, UNIT_NAME_ORDER);
        SourceInfo si = crsc.getSourceInfo();
        Index decl2num = new Index(HashCode.IDENTITY);
        EvaluationResult res = new EvaluationResult();
        for (int i = 0, n = 0; i < uarray.length; i += 1) {
            TreeWalker tw = new TreeWalker(uarray[i]);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if (pe instanceof Declaration) {
                    decl2num.put(pe, n);
                }
                n += 1;
            }
        }
        StringBuffer line = new StringBuffer(1024);
        int number = 1;
        for (int i = 0; i < uarray.length; i += 1) {
            CompilationUnit unit = uarray[i];
            TreeWalker tw = new TreeWalker(unit);
            Position oldPos = Position.UNDEFINED;
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                line.append("("+(pe.getComments() == null ? 0 : pe.getComments().size()) + " comments)");
                //line.append(number);
                //line.append(' ');
                Position pos = pe.getFirstElement().getStartPosition();
                if (!pos.equals(oldPos)) {
                    //line.append(pos); // we're not really interested in exact positions
                    oldPos = pos;
                }
                line.append(' ');
                String name = pe.getClass().getName();
                name = name.substring(name.lastIndexOf('.') + 1);
                for (int k = 0, s = name.length(); k < s; k += 1) {
                    char c = name.charAt(k);
                    if (Character.isUpperCase(c)) {
                        line.append(c);
                    }
                }
                if (pe instanceof CompilationUnit) {
                    line.append(Format.toString(" \"%u\"", pe));
                }
                if (pe instanceof Expression) {
                    Type t = si.getType(pe);
                    if (t != null) {
                        line.append(" :");
                        if (t instanceof ProgramElement) {
                            line.append(decl2num.get(t));
                        } else {
                            line.append(Format.toString("%N", t));
                        }
                        if (crsc.getConstantEvaluator().isCompileTimeConstant((Expression) pe, res)) {
                            line.append(" ==" + res.toString());
                        }
                    }
                }
                int ref = -1;
                if (pe instanceof Constructor) {
                	ref = crsc.getCrossReferenceSourceInfo().getReferences((Constructor)pe).size();
                }
                if (pe instanceof Field) {
                	ref = crsc.getCrossReferenceSourceInfo().getReferences((Field)pe).size();
                }
                if (pe instanceof Method) {
                	ref = crsc.getCrossReferenceSourceInfo().getReferences((Method)pe).size();
                }
                if (pe instanceof Type) {
                	ref = crsc.getCrossReferenceSourceInfo().getReferences((Type)pe).size();
                }
                if (pe instanceof Variable) {
                	ref = crsc.getCrossReferenceSourceInfo().getReferences((Variable)pe).size();
                }
                if (ref != -1)
                	line.append("("+ref+" refs)");
                
                ProgramModelElement dest = null;
                if (pe instanceof ConstructorReference) {
                    dest = si.getConstructor((ConstructorReference) pe);
                } else if (pe instanceof MethodReference) {
                    dest = si.getMethod((MethodReference) pe);
                } else if (pe instanceof VariableReference) {
                    dest = si.getVariable((VariableReference) pe);
                } else if (pe instanceof TypeReference) {
                    dest = si.getType((TypeReference) pe);
                } else if (pe instanceof PackageReference) {
                    dest = si.getPackage((PackageReference) pe);
                }
                if (dest != null) {
                    line.append(" ->");
                    if (dest instanceof ProgramElement) {
                        line.append(decl2num.get(dest));
                    } else {
                        line.append(Format.toString("%N", dest));
                    }
                }
                line.append("\n");
                out.write(line.toString());
                line.setLength(0);
                number += 1;
            }
        }
        out.flush();
    }
    
    
    
//    public void testEvo3() {
//        crsc = new CrossReferenceServiceConfiguration();
//        dsfr = new DefaultSourceFileRepository(crsc);
//        crsc.getProjectSettings().addPropertyChangeListener(dsfr);
//        crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, 
//				new File("D:/workspace/EVO3/src").getAbsolutePath() +
//				File.pathSeparatorChar + new File("D:/workspace/EVO3/test").getAbsolutePath() +
//				File.pathSeparatorChar + "D:/workspace/EVO3/lib/review.jar" +
//				File.pathSeparatorChar + "D:/workspace/EVO3/lib/junit.jar" +
//				File.pathSeparatorChar + "D:/workspace/EVO3/lib/recoder.jar" +
//				File.pathSeparatorChar + "D:/workspace/EVO3/lib/srfgenerator.jar" +
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jce.jar" + 
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jsse.jar " +
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "rt.jar"  
//        );
//        crsc.getProjectSettings().ensureExtensionClassesAreInPath();
//        crsc.getProjectSettings().ensureSystemClassesAreInPath();
//        dsfr.initialize(crsc);
//        
//        crsc.getProjectSettings().getErrorHandler().setErrorThreshold(9999);
//        
//        runIt();
//        
//        TypeDeclaration td = (TypeDeclaration)crsc.getNameInfo().getClassType("de.fzi.evo3.datamodel.DAccessPath");
////        MethodList ml = td.getMethods();
////        for (int i = 0; i < ml.size(); i++) {
////        	MethodDeclaration md = (MethodDeclaration)ml.getMethod(i);
////        	int refNum = crsc.getCrossReferenceSourceInfo().getReferences(md).size();
////        	if (refNum == 0)
////        		System.err.println(md.toSource() + " is referenced " + refNum + " times");
////        }
//        List<Field> vl = td.getFields();
//        for (int i = 0; i < vl.size(); i++) {
//        	FieldSpecification fs = (FieldSpecification)vl.getField(i);
//        		int refNum = crsc.getCrossReferenceSourceInfo().getReferences(fs).size();
//        		//if (refNum == 0)
//        			System.err.println("a fieldspec of " + fs.toSource() + " is referenced " + refNum + " times");
//        }
//    }
}
