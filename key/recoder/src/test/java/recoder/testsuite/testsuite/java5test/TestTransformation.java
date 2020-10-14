package recoder.testsuite.testsuite.java5test;

import java.io.File;
import java.io.IOException;
import java.util.List;

import junit.framework.TestCase;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.PropertyNames;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
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
import recoder.kit.transformation.java5to4.methodRepl.ReplaceOthers;
import recoder.util.ProgressEvent;

public class TestTransformation extends TestCase {
    private CrossReferenceServiceConfiguration crsc;
    private SourceFileRepository dsfr;
    
//    public void testTransformation() {
//    	// initialize CrossReferenceServiceConfiguration and SourceFileRepository
//    	crsc = new CrossReferenceServiceConfiguration();
//    	dsfr = crsc.getSourceFileRepository();
//    	crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH,
//    			new File("/Users/tamarasteijger/Meine_Dateien/Uni/Programmier_Praktikum/Uebung3/").getAbsolutePath() +
//    			File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jce.jar" + 
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jsse.jar " +
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "rt.jar"  +
//				File.pathSeparatorChar + "test/java5/src/prettyprinting/testcode/java/lib/namensfehler.jar"		
//    	);
//    	crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH,
//    			new File("mara/src/output/").getAbsolutePath());
//    	crsc.getProjectSettings().ensureExtensionClassesAreInPath();
//    	crsc.getProjectSettings().ensureSystemClassesAreInPath();
//    	
//        crsc.getProjectSettings().setProperty(ProjectSettings.JAVA_5, "true");
//        crsc.getProjectSettings().setProperty(ProjectSettings.TABSIZE, "4");
//        try {
//            dsfr.getAllCompilationUnitsFromPath();
//            crsc.getChangeHistory().updateModel();
//        } catch (ParserException pe) {
//            System.err.println(pe.getMessage());
//            fail("unexpected ParserException");
////        } finally {
////            crsc.getProjectSettings().setProperty(ProjectSettings.Java_5, Boolean.toString(b));
//        }
//        List<CompilationUnit> cul = dsfr.getCompilationUnits();
//        for (int i = 0; i < cul.size(); i++) {
//        	cul.get(i).validateAll();
//        }
//        
//        System.out.println("Starting transformation");
//        for (CompilationUnit cu:cul){
//        	TestTransformation tt = new TestTransformation(crsc, cu);
//        	tt.execute();
//        	System.out.println("");
//        }
//        
//        try {
//            dsfr.printAll(true);
//        } catch (IOException e) {
//            fail();
//        }
//    }
    
    private void setPath(String base) {
//   	 initialize CrossReferenceServiceConfiguration and SourceFileRepository
    	crsc = new CrossReferenceServiceConfiguration();
    	dsfr = crsc.getSourceFileRepository();
    	crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH,
    			//"../pmd/src/;../pmd/lib/*.jar;C:/libs/apache-ant-1.7.1/lib/*.jar"
    			//"src/;3rdpartylibs/*.jar"
    			//new File("test/java5/input/" + base + "/").getAbsolutePath() +
    			//new File("test/java5/src/transformations").getAbsolutePath() +
    					"../findbugs/src/"+File.pathSeparatorChar+
    					"../findbugs/lib/*.jar"+File.pathSeparatorChar+
    					"3rdpartylibs/*.jar"
//    					
//    					).getAbsolutePath() +
//    			//new File("src/recoder/"+File.pathSeparatorChar+"test/src/"+File.pathSeparatorChar+
//    			//		"doc/examples/src/"+File.pathSeparatorChar+"3rdpartylibs/junit.jar"+
//    			//		File.pathSeparatorChar+"3rdpartylibs/bsh-1.2b2.jar").getAbsolutePath() +
//    			File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jce.jar" + 
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "jsse.jar " +
//				File.pathSeparatorChar + System.getProperty("java.home") + File.separatorChar + "lib" + File.separator + "rt.jar"  +
//				File.pathSeparatorChar + "test/java5/src/prettyprinting/testcode/java/lib/namensfehler.jar"		
    	);
    	crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH,
//    			new File("test/java5/output/" + base + "/").getAbsolutePath());
//    			new File("test/java5/output/transformations/").getAbsolutePath());
    			new File("c:/temp/pmd/").getAbsolutePath());
    	crsc.getProjectSettings().ensureExtensionClassesAreInPath();
    	crsc.getProjectSettings().ensureSystemClassesAreInPath();
    	
  			
    	class MyPL implements recoder.util.ProgressListener {
    		// TODO remove again...
    		int last;
    		public void workProgressed(ProgressEvent pe) {
    			if (pe.getWorkToDoCount() == 0)
    				return;
    			int cur = pe.getWorkDoneCount()*100 / pe.getWorkToDoCount();
    			if (cur != last) {
    				System.out.println(cur);
    				last = cur;
    			}
//    			if (cur == 86 && STOP)
//    				System.out.println();
    		}

    	}

		crsc.getSourceFileRepository().addProgressListener(new MyPL());
		crsc.getSourceInfo().addProgressListener(new MyPL());
    	//crsc.getSourceFileRepository().addProgressListener(pl);
    }
    
    boolean STOP = false; // TODO remove !!
    
    public void runIt() {
    	crsc.getProjectSettings().setProperty(PropertyNames.JAVA_5, "true");
        crsc.getProjectSettings().setProperty(PropertyNames.TABSIZE, "4");
        try {
            dsfr.getAllCompilationUnitsFromPath();
            System.out.println("Parsing done"); // TODO remove
            STOP = true; // TODO remove
            crsc.getChangeHistory().updateModel();
        } catch (ParserException pe) {
            System.err.println(pe.getMessage());
            fail("unexpected ParserException");
//        } finally {
//            crsc.getProjectSettings().setProperty(ProjectSettings.Java_5, Boolean.toString(b));
        }
        List<CompilationUnit> cul = dsfr.getCompilationUnits();
        for (int i = 0; i < cul.size(); i++) {
//        	if (cul.get(i).getName().equals("FILE:/Users/tamarasteijger/Meine_Dateien/Schweden/Kurse/Master/RECODER/../findbugs-1.3.4/src/java/edu/umd/cs/findbugs/ba/jsr305/FlowValue.java"))
//        			System.out.println(cul.get(i).getName());
        	cul.get(i).validateAll();
        	if (i%80 == 0) System.out.println();
        	System.out.print('.');
        }
    }
    
    private void writeBack() {
        try {
            dsfr.printAll(true);
        } catch (IOException e) {
            fail();
        }
    }
    
    public void testAllTransformations() {
    	setPath("");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	
    	System.out.println("Conditionals");
    	MakeConditionalCompatible mcc = new MakeConditionalCompatible(crsc, cul);
    	mcc.execute();
    	
    	System.out.println("Enhanced For");
    	EnhancedFor2For eff = new EnhancedFor2For(crsc, cul);
    	eff.execute();
//    	writeBack();
    	
    	System.out.println("Generics");
    	ResolveGenerics rg = new ResolveGenerics(crsc, cul);
    	rg.execute();
//    	writeBack();
    	
    	System.out.println("Covariant Return Types");
    	RemoveCoVariantReturnTypes rc = new RemoveCoVariantReturnTypes(crsc, cul);
    	rc.execute();
//    	writeBack();
    	
    	System.out.println("Annotations");
    	RemoveAnnotations ra = new RemoveAnnotations(crsc, cul);
    	ra.execute();
//    	writeBack();
    	
    	System.out.println("Static Imports");
    	RemoveStaticImports rsi = new RemoveStaticImports(crsc, cul);
    	rsi.execute();
//    	writeBack();
    	
    	System.out.println("Boxing");
    	ResolveBoxing rb = new ResolveBoxing(crsc, cul);
    	rb.execute();
//    	writeBack();
    	
    	System.out.println("Varargs");
    	ResolveVarArgs rva = new ResolveVarArgs(crsc, cul);
    	rva.execute();
//    	writeBack();
    	
    	System.out.println("Enumerations");
    	ReplaceEnums re = new ReplaceEnums(crsc, cul);
    	re.execute();
//    	writeBack();
    	
    	System.out.println("ReplaceEmptyCollection");
    	ReplaceEmptyCollections rec = new ReplaceEmptyCollections(crsc);
    	rec.execute();

    	System.out.println("RetroLibs");
    	ApplyRetrotranslatorLibs arl = new ApplyRetrotranslatorLibs(crsc);
    	arl.execute();
    	
    	System.out.println("Others...");
    	ReplaceOthers ro = new ReplaceOthers(crsc);
    	ro.execute();
    	
    	writeBack();
    }

 	public void testAnnotations() {
    	setPath("annotationtest");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
        System.out.println("Annotation Test:");
        RemoveAnnotations ra = new RemoveAnnotations(crsc, cul);
        ra.execute();
//        for (CompilationUnit cu:cul){
//        	RemoveAnnotations ra = new RemoveAnnotations(crsc, cu);
//        	ra.execute();
//        	System.out.println("");
//        }
        
        writeBack();
    }
    
    
    public void testCovariantReturns() {
    	setPath("CoVariantReturnTypes");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	
    	System.out.println("CovariantReturnTypes Test:");
    	RemoveCoVariantReturnTypes rc = new RemoveCoVariantReturnTypes(crsc,cul);
    	rc.execute();
    	
//    	crsc.getChangeHistory().updateModel();
    	
//    	crsc.getChangeHistory().rollback();
    	writeBack();
    }

    
    public void testEnhancedFor2For() {
    	setPath("EnhancedFor");
    	runIt();
    	System.out.println("EnhancedFor2For:");
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	EnhancedFor2For eff;
    	eff = new EnhancedFor2For(crsc,cul);
    	eff.execute();
//    	NonTerminalProgramElement root;
//    	for (CompilationUnit cu:cul) {
//    		root = cu;
//    		TreeWalker tw = new TreeWalker(root);
//    		while (tw.next()) {
//    			ProgramElement pe = tw.getProgramElement();
//    			if (pe instanceof EnhancedFor) {
//    				eff = new EnhancedFor2For(crsc,(EnhancedFor)pe);
//    				eff.execute();
//    			}
//    		} 
//    	}
//    	crsc.getChangeHistory().rollback();
    	
    	writeBack();
    }
    
    
    public void testRemoveStaticImports() {
    	setPath("StaticImports");
    	runIt();
    	
    	List<CompilationUnit> cul= dsfr.getCompilationUnits();
    	RemoveStaticImports rsi = new RemoveStaticImports(crsc, cul);
    	rsi.execute();
//    	RemoveStaticImports rsi;
//    	for (CompilationUnit cu: cul) {
//    		rsi = new RemoveStaticImports(crsc, cu);
//    		rsi.execute();
//    	}
//    	crsc.getChangeHistory().rollback();
    	
    	writeBack();
    }
	
    
    public void testMakeConditionalCompatible() {
    	setPath("Conditionals");
    	runIt();
    	System.out.println("Conditionals:");
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	MakeConditionalCompatible mcc = new MakeConditionalCompatible(crsc, cul);
    	mcc.execute();
//    	MakeConditionalCompatible mcc;
//    	for (CompilationUnit cu : cul) {
//    		mcc = new MakeConditionalCompatible(crsc, cu);
//    		mcc.execute();
//    	}
    	writeBack();
    }
    
    
    public void testResolveBoxing() {
    	setPath("Boxing");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	ResolveBoxing rb = new ResolveBoxing(crsc, cul);
    	rb.execute();
//    	ResolveBoxing rb;
//    	for (CompilationUnit cu : cul) {
//    		rb = new ResolveBoxing(crsc, cu);
//    		rb.execute();
//    	}
//    	crsc.getChangeHistory().rollback();
    	
    	writeBack();
    }
    
    
    public void testResolveVarArgs() {
    	setPath("VarArgs");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	ResolveVarArgs rva = new ResolveVarArgs(crsc, cul);
    	rva.execute();
//    	ResolveVarArgs rva;
//    	for (CompilationUnit cu : cul) {
//    		rva = new ResolveVarArgs(crsc, cu);
//    		rva.execute();
//    	}
//    	crsc.getChangeHistory().rollback();
    	
    	writeBack();
    }
    
    
    public void testReplaceEnums() {
    	setPath("Enumerations");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	ReplaceEnums re = new ReplaceEnums(crsc, cul);
    	re.execute();
//    	ReplaceEnums re;
//    	for (CompilationUnit cu : cul) {
//    		re = new ReplaceEnums(crsc, cu);
//    		re.execute();
//    	}
//    	crsc.getChangeHistory().rollback();
    	
    	writeBack();
    }
    
    
    public void testGenerics() {
    	setPath("Generics");
    	runIt();
    	
    	List<CompilationUnit> cul = dsfr.getCompilationUnits();
    	ResolveGenerics rg = new ResolveGenerics(crsc, cul);
    	rg.execute();
//    	ResolveGenerics rg;
//    	for (CompilationUnit cu : cul) {
//    		rg = new ResolveGenerics(crsc, cu);
//    		rg.execute();
//    	}
//    	crsc.getChangeHistory().rollback();
    	
    	writeBack();
    }

}
