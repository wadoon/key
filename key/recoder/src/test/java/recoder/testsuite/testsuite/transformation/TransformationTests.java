/*
 * Created on 11.03.2005

 *
 * This file is part of the RECODER library and protected by the LGPL.
 */
package recoder.testsuite.testsuite.transformation;
import java.io.File;
import java.io.IOException;
import java.util.List;

import junit.framework.TestCase;
import junit.framework.TestResult;
import junit.framework.TestSuite;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.abstraction.Method;
import recoder.io.DefaultSourceFileRepository;
import recoder.io.PropertyNames;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.StatementBlock;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.java.reference.TypeReference;
import recoder.kit.NoProblem;
import recoder.kit.transformation.java5to4.methodRepl.ReplaceEmptyCollections;
import recoder.service.ChangeHistory;
import recoder.service.NameInfo;
import recoder.service.SemanticsChecker;


/**
 * @author gutzmann
 *
 * Tests some transformations.
 */
public class TransformationTests extends TestCase {
    private CrossReferenceServiceConfiguration crsc;
    private DefaultSourceFileRepository dsfr;
    private boolean silent = true;
    
    public static void main(String args[]) {
        TestSuite testSuite = new TestSuite(TransformationTests.class);
        TestResult result = new TestResult();
        testSuite.run(result);
        System.out.println("Number of errors: " + result.errorCount() + " / " + result.runCount());
        System.out.println("Number of failures: " + result.failureCount() + " / " + result.runCount());
    }

    
    private void setPath(String base) {
        crsc = new CrossReferenceServiceConfiguration();
        dsfr = (DefaultSourceFileRepository)crsc.getSourceFileRepository();
        crsc.getProjectSettings().addPropertyChangeListener(dsfr);
        crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, 
				new File("test/transformation/" + base + "/").getAbsolutePath());
        crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH,
                new File("test/transformation/output/" + base + "/").getAbsolutePath());
        crsc.getProjectSettings().ensureSystemClassesAreInPath();
    }
    
    private void runIt() {
        try {
            dsfr.getAllCompilationUnitsFromPath();
            crsc.getChangeHistory().updateModel();
            for (CompilationUnit cu : dsfr.getCompilationUnits()) {
            	cu.validateAll();
            }
            new SemanticsChecker(crsc).checkAllCompilationUnits();
        } catch (ParserException pe) {
            System.err.println(pe.getMessage());
            fail("unexpected ParserException");
        }
    }
    private void writeBack() {
        try {
            dsfr.printAll(true);
        } catch (IOException e) {
            fail();
        }
    }
    
    public void testObfuscater() {
        setPath("obfuscate");
        runIt();
        //Obfuscate of = new Obfuscate(crsc);
        //if (of.analyze() instanceof NoProblem)
        //    of.transform();
        // TODO write back and compare!
    }
    
    public void testReadOnly() {
    	setPath("readOnly");
    	runIt();
    	
    	List<TypeReference> trl = crsc.getCrossReferenceSourceInfo().getReferences(crsc.getNameInfo().getType("Test"));
    	for (int i = 0; i < trl.size(); i++) {
    		TypeReference tr = trl.get(i);
    		if (!silent)
    			System.out.println(tr.toSource());
    	}
    }
    
    private void defaultConstructorReferences(VisibilityModifier vm) {
    	setPath("defaultCons");
    	runIt();
    	// add a constructor now
    	ChangeHistory ch = crsc.getChangeHistory();
    	NameInfo ni = crsc.getNameInfo();
    	ClassDeclaration cd = (ClassDeclaration)ni.getType("DefaultCons");
    	ConstructorDeclaration cons = new ConstructorDeclaration(vm, new Identifier("DefaultCons"),
    			null, null, new StatementBlock());
    	cd.getMembers().add(cons);
    	cd.makeParentRoleValid();
    	ch.attached(cons);
    	ch.updateModel();
    	for (CompilationUnit cu : dsfr.getCompilationUnits()) {
    		cu.validateAll();
    	}
    	// now, the default constructor no longer exists.
    	// The added constructor should be referenced, however, if it is still visible, 
    	// and an error should occur if not.
    	// TODO Recoder does not check visibility yet! So this works fine for both cases (for now)!
    	
    	int newref = crsc.getCrossReferenceSourceInfo().getReferences(cons).size();
		System.out.println(newref);
    	
    	MethodDeclaration md = (MethodDeclaration)cd.getMethods().get(0); // main()
     }
    
    public void testDefaultConstructorReferences1() {
    	defaultConstructorReferences(new Public());
    }
    public void testDefaultConstructorReferences2() {
    	defaultConstructorReferences(new Private());
    }
    
    public void testReplaceEmptyCollections() {
    	setPath("emptyCollections");
    	runIt();
    	ClassType coll = crsc.getNameInfo().getClassType("java.util.Collections");
    	checkFRefCnt(coll, "EMPTY_LIST", 0);
    	checkFRefCnt(coll, "EMPTY_MAP", 0);
    	checkFRefCnt(coll, "EMPTY_SET", 0);
    	checkFRefCnt(coll, "emptyList", 2);
    	checkFRefCnt(coll, "emptyMap", 2);
    	checkFRefCnt(coll, "emptySet", 2);
    	new ReplaceEmptyCollections(crsc).execute();
    	crsc.getChangeHistory().updateModel();
    	checkFRefCnt(coll, "EMPTY_LIST", 2);
    	checkFRefCnt(coll, "EMPTY_MAP", 2);
    	checkFRefCnt(coll, "EMPTY_SET", 2);
    	checkFRefCnt(coll, "emptyList", 0);
    	checkFRefCnt(coll, "emptyMap", 0);
    	checkFRefCnt(coll, "emptySet", 0);    	
    }
    // helper method for testReplaceEmptyCollections
    private void checkFRefCnt(ClassType coll, String memberName, int cnt) {
    	boolean found = false;
    	for (Field f : coll.getFields()) {
    		if (memberName.equals(f.getName())) {
    			assertTrue(cnt == crsc.getCrossReferenceSourceInfo().getReferences(f).size());
    			found = true;
    			break;
    		}
    	}
    	if (!found) {
        	for (Method m : coll.getMethods()) {
        		if (memberName.equals(m.getName())) {
        			assertTrue(cnt == crsc.getCrossReferenceSourceInfo().getReferences(m).size());
        			found = true;
        			break;
        		}
        	}    		
    	}
    	assertTrue(found);
    }
}
