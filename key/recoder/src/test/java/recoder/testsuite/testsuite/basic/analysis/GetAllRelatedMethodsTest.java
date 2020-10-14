package recoder.testsuite.testsuite.basic.analysis;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import junit.framework.TestCase;
import recoder.abstraction.ClassType;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.kit.MethodKit;
import recoder.service.CrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.testsuite.testsuite.basic.BasicTestsSuite;

public class GetAllRelatedMethodsTest extends TestCase {
    CrossReferenceSourceInfo xrsi;

    NameInfo ni;

    final static String PACKAGE = "testdata.";

    private ClassType loadClass(String localname) {
        String name = PACKAGE + localname;
        ClassType ct = ni.getClassType(name);
        if (ct == null) {
            Assert.fail("Could not load test data " + name);
        }
        return ct;
    }

    public void testGetAllRelatedMethodsTest() throws Exception {
        this.xrsi = BasicTestsSuite.config.getCrossReferenceSourceInfo();
        this.ni = BasicTestsSuite.config.getNameInfo();

        // preload main class (makes the other types visible, too)
        loadClass("MethodTestData");

        ClassType ct = loadClass("Child");
        checkRelatedMethodsCount(ct, "childMethod", 1);
        checkRelatedMethodsCount(ct, "baseAndChildMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndChildAndIFirstMethod", 3);
        checkRelatedMethodsCount(ct, "baseAndIFirstMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndIFirstISecondMethod", 3);

        ct = loadClass("IFirst");
        checkRelatedMethodsCount(ct, "childAndIFirstMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndChildAndIFirstMethod", 3);
        checkRelatedMethodsCount(ct, "baseAndIFirstMethod", 2);
        //checkRelatedMethodsCount(ct, "clone",3); // Should be all classes
        // overriding clone

        ct = loadClass("Base");
        checkRelatedMethodsCount(ct, "childMethod", 0);
        checkRelatedMethodsCount(ct, "baseAndChildMethod", 2);
        checkRelatedMethodsCount(ct, "baseAndChildAndIFirstMethod", 3);
        checkRelatedMethodsCount(ct, "baseAndIFirstMethod", 2);
    }

    private void checkRelatedMethodsCount(ClassType ct, String methodName, int expectedNumber) {
        List<Method> ml = MethodKit.getAllRelatedMethods(ni, xrsi, ct, methodName, new ArrayList<Type>(0));
        if (ml.size() != expectedNumber) {
        	System.err.println("Aha");
        }
        Assert.assertEquals(methodName, expectedNumber, ml.size());
        checkSignatures(ml, methodName, new ArrayList<Type>(0));
    }

    private void checkSignatures(List<Method> ml, String methodName, List<Type> signature) {
        for (int i = 0; i < ml.size(); i++) {
            Method method = ml.get(i);
            Assert.assertEquals(method.getName(), methodName);
            Assert.assertEquals(method.getSignature(), signature);
        }
    }

}
