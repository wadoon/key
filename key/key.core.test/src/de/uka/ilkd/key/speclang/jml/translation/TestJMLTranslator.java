// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.translation;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.Map;

import junit.framework.TestCase;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.LogicVariable;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.HelperClassForTests;



public class TestJMLTranslator extends TestCase {

    public static final String testFile = HelperClassForTests.TESTCASE_DIRECTORY
                                          + File.separator + "speclang"
                                          + File.separator + "testFile.key";
    private static TermBuilder TB;
    private static JavaInfo javaInfo;
    private static Services services;
    private static KeYJavaType testClassType;
    private static Map<LocationVariable,JavaDLTerm> atPres = new LinkedHashMap<LocationVariable,JavaDLTerm>();


    @Override
    protected synchronized void setUp() {        
        if (javaInfo == null) {
            javaInfo = new HelperClassForTests().parse(
                    new File(testFile)).getFirstProof().getJavaInfo();
            services = javaInfo.getServices();
            TB = services.getTermBuilder();
            testClassType = javaInfo.getKeYJavaType("testPackage.TestClass");
            atPres.put(services.getTheories().getHeapLDT().getHeap(), TB.var(TB.heapAtPreVar("heapAtPre", services.getTheories().getHeapLDT().getHeap().sort(),
                    false)));

        }
    }


    @Override
    protected void tearDown() {
    }


    protected ProgramVariable buildSelfVarAsProgVar() {
        ProgramElementName classPEN = new ProgramElementName("self");
        ProgramVariable result = new LocationVariable(classPEN, testClassType);
        return result;
    }


    protected ProgramVariable buildExcVar() {
        KeYJavaType excType = javaInfo.getTypeByClassName("java.lang.Throwable");
        ProgramElementName excPEN = new ProgramElementName("exc");
        return new LocationVariable(excPEN, excType);
    }


    protected ProgramVariable buildResultVar(IProgramMethod pm) {
        ProgramElementName resPEN = new ProgramElementName("result");
        ProgramVariable result = new LocationVariable(resPEN,
                                                      pm.getReturnType());
        return result;
    }


    private boolean termContains(JavaDLTerm t,
                                 JavaDLTerm sub) {

        for (int i = 0; i < t.arity(); i++) {
            if (t.sub(i).equals(sub) || termContains(t.sub(i), sub)) {
                return true;
            }
        }

        return false;
    }


    private boolean termContains(JavaDLTerm t,
                                 Operator op) {

        if (t.op().arity() == op.arity() && t.op().name().equals(op.name())) {
            return true;
        }

        for (int i = 0; i < t.arity(); i++) {
            if (termContains(t.sub(i), op)) {
                return true;
            }
        }

        return false;
    }


    public void testTrueTerm() {
        JavaDLTerm result = null;

        try {
            result = JMLTranslator.translate(new PositionedString("true"),
                                             testClassType, null, null, null,
                                             null, null, JavaDLTerm.class,
                                             services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.equals(TB.tt()));
    }


    public void testSelfVar() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(new PositionedString("this"),
                                             testClassType, selfVar, null, null,
                                             null, null, JavaDLTerm.class,
                                             services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.equals(TB.var(selfVar)));
    }


    public void testLogicalExpression() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "(b <= s &&  i > 5) ==> this != instance"), testClassType,
                                                    selfVar, null, null, null,
                                                    null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Junctor.IMP));
        assertTrue(result.sub(0).op().equals(Junctor.AND));
        assertTrue(termContains(result, TB.zTerm("5")));
        assertTrue(termContains(result, selfVar));
    }

    // There is a problem with spaces here.
    // Adding spaces around "j < i" solves the problem.
    // see bug #1548
    public void testSumParsing() throws SLTranslationException {
        ProgramVariable selfVar = buildSelfVarAsProgVar();
        JMLTranslator.translate(new PositionedString(
                "0 == ((\\sum int j; 0<=j && j<i; j))"),
                testClassType, selfVar, null, null, null, null, JavaDLTerm.class, services);
    }


    public void testPrimitiveField() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "this.i"), testClassType,
                                             selfVar, null, null, null,
                                             null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        //assertTrue(termContains(result.getFormula(), AttributeOp.getAttributeOp(i) ));
        assertTrue(termContains(result, selfVar));
    }


    public void testSimpleQuery() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        IProgramMethod getOne = javaInfo.getProgramMethod(testClassType,
                                                         "getOne",
                                                         ImmutableSLList.<KeYJavaType>nil(),
                                                         testClassType);

        try {
            result = JMLTranslator.translate(new PositionedString("this.getOne()"),
                                             testClassType, selfVar, null,
                                             null, null, null, JavaDLTerm.class,
                                             services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(termContains(result, selfVar));
        assertTrue(termContains(result, getOne));
    }


    public void testForAll() {
        JavaDLTerm result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\forall int i; (0 <= i && i <= 2147483647) )"),
                    testClassType, null, null, null, null,
                    null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Quantifier.ALL));
        assertTrue(termContains(result, TB.zTerm("2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) services.getNamespaces().sorts().lookup(new Name(
                "int")));
        JavaDLTerm expected =
                TB.all(i,
                       TB.imp(TB.inInt(TB.var(i)),
                              TB.and(TB.leq(TB.zTerm("0"),
                                            TB.var(i)),
                                     TB.leq(TB.var(i),
                                            TB.zTerm("2147483647")))));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }


    public void testForEx() {
        JavaDLTerm result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\exists int i; (0 <= i && i <= 2147483647) )"),
                    testClassType, null, null, null, null,
                    null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Quantifier.EX));
        assertTrue(termContains(result, TB.zTerm("2147483647")));
        assertTrue(termContains(result, Junctor.AND));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) services.getNamespaces().sorts().lookup(new Name(
                "int")));
        JavaDLTerm expected =
                TB.ex(i,
                      TB.and(TB.inInt(TB.var(i)),
                             TB.and(TB.leq(TB.zTerm("0"),
                                           TB.var(i)),
                                    TB.leq(TB.var(i),
                                           TB.zTerm("2147483647")))));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }


    public void testBsumInt() {
        JavaDLTerm result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\bsum int i; 0; 2147483647; i)"),
                    testClassType, null, null, null, null,
                    null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        NamespaceSet nss = services.getNamespaces();
        Function q = (Function) nss.functions().lookup(new Name("bsum"));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) nss.sorts().lookup(new Name("int")));
        JavaDLTerm expected =
                TB.func(services.getTheories().getIntegerLDT().getJavaCastInt(),
                TB.bsum(i,
                        TB.zTerm("0"),
                        TB.zTerm("2147483647"),
                        TB.var(i)));
        assertTrue(result != null);
        assertSame(q, result.sub(0).op());
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }


    public void testBsumBigInt() {
        JavaDLTerm result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\bsum \\bigint i; 0; 2147483647; i)"),
                    testClassType, null, null, null, null,
                    null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(e.getMessage(), false);
        }

        NamespaceSet nss = services.getNamespaces();
        Function q = (Function) nss.functions().lookup(new Name("bsum"));
        LogicVariable i =
                new LogicVariable(new Name("i"),
                                  (Sort) nss.sorts().lookup(new Name("int")));
        JavaDLTerm expected =
                TB.bsum(i,
                        TB.zTerm("0"),
                        TB.zTerm("2147483647"),
                        TB.var(i));
        assertTrue(result != null);
        assertSame(q, result.op());
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                   result.equalsModRenaming(expected));
    }
    
    public void testInfiniteUnion() {
        JavaDLTerm result = null;
        final String input = "\\infinite_union(Object o; \\empty)";
        try {
            result = JMLTranslator.translate(input, testClassType, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            fail(""+e);
        }
        assertNotNull(result);
        Operator unionOp = services.getTheories().getLocSetLDT().getInfiniteUnion();
        LogicVariable o =
                        new LogicVariable(new Name("o"), services.getProgramServices().getJavaInfo().getJavaLangObject().getSort());
        assertSame(unionOp, result.op());
        JavaDLTerm guard = TB.and( TB.convertToFormula(TB.created(TB.var(o))), TB.not(TB.equals(TB.var(o), TB.NULL())));
        JavaDLTerm expected = TB.infiniteUnion(new QuantifiableVariable[]{o}, TB.ife(guard, TB.empty(), TB.empty()));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                        result.equalsModRenaming(expected));
    }

    public void testInfiniteUnion2() {
        JavaDLTerm result = null;
        final String input = "\\infinite_union(nullable Object o; \\empty)";
        try {
            result = JMLTranslator.translate(input, testClassType, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            fail(""+e);
        }
        assertNotNull(result);
        Operator unionOp = services.getTheories().getLocSetLDT().getInfiniteUnion();
        LogicVariable o =
                        new LogicVariable(new Name("o"), services.getProgramServices().getJavaInfo().getJavaLangObject().getSort());
        assertSame(unionOp, result.op());
        JavaDLTerm guard = TB.or( TB.convertToFormula(TB.created(TB.var(o))), TB.equals(TB.var(o), TB.NULL()));
        JavaDLTerm expected = TB.infiniteUnion(new QuantifiableVariable[]{o}, TB.ife(guard, TB.empty(), TB.empty()));
        assertTrue("Result was: " + result + "; \nExpected was: " + expected,
                        result.equalsModRenaming(expected));
    }


    public void testComplexExists() {
        JavaDLTerm result = null;

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "(\\exists TestClass t; t != null; t.i == 0)"),
                    testClassType, null, null, null, null,
                    null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue("Error Message: " + e, false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Quantifier.EX));
        assertTrue(result.sub(0).op().equals(Junctor.AND));
        assertTrue(termContains(result, TB.NULL()));
    }


    public void testOld() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();
        ProgramVariable i = javaInfo.getAttribute("testPackage.TestClass::i");


        try {
            result = JMLTranslator.translate(new PositionedString(
                    "this.i == \\old(this.i)"),
                                                    testClassType, selfVar, null,
                                                    null, excVar, atPres, 
                                                    JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(
                termContains(result,
                             services.getTheories().getHeapLDT().getHeap()));
        assertTrue(termContains(result, atPres.get(services.getTheories().getHeapLDT().getHeap()).op()));
    }


    public void testResultVar() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable excVar = buildExcVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "getOne",
                                                     signature, testClassType);

        ProgramVariable resultVar = buildResultVar(pm);

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "\\result == 1"),
                                                    testClassType, selfVar, null,
                                                    resultVar, excVar, atPres, 
                                                    JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(termContains(result, resultVar));

    }


    public void testNonNullElements() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        ProgramVariable array = javaInfo.getAttribute(
                "testPackage.TestClass::array");

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "\\nonnullelements(this.array)"),
                                                    testClassType,
                                                    selfVar,
                                                    null,
                                                    null,
                                                    null,
                                                    atPres, JavaDLTerm.class,
                                                    services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        //assertTrue(termContains(result.getFormula(), AttributeOp.getAttributeOp(array)));
        assertTrue(termContains(result, TB.NULL()));
    }


    public void testIsInitialized() {

        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "\\is_initialized(testPackage.TestClass)"),
                                                    testClassType,
                                                    selfVar,
                                                    null,
                                                    null,
                                                    null,
                                                    atPres, JavaDLTerm.class,
                                                    services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(termContains(result, TB.var(
                javaInfo.getAttribute(
                ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED,
                                      testClassType))));
    }


    public void testHexLiteral() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(
                    new PositionedString(" i == 0x12 "),
                    testClassType, selfVar, null, null, null, null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.op().equals(Equality.EQUALS));
        assertTrue(termContains(result, TB.zTerm("18")));
    }


    public void testComplexQueryResolving1() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo.getKeYJavaType(
                PrimitiveType.JAVA_INT));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                                                     signature, testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString("this.m((int)4 + 2) == this.m(i)"),
                    testClassType,
                    selfVar, null, null, null, null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
        assertTrue(result.sub(1).op().equals(pm));
    }


    public void testComplexQueryResolving2() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo.getKeYJavaType(
                PrimitiveType.JAVA_LONG));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                                                     signature, testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString("this.m(l) == this.m((long)i + 3)"),
                    testClassType, selfVar,
                    null, null, null, null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
        assertTrue(result.sub(1).op().equals(pm));
    }


    public void testComplexQueryResolving3() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();
        signature = signature.append(javaInfo.getKeYJavaType(
                PrimitiveType.JAVA_INT));

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType, "m",
                                                     signature, testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString("this.m(s + 4) == this.m(+b)"),
                    testClassType, selfVar,
                    null, null, null, null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
        assertTrue(result.sub(1).op().equals(pm));
    }


    public void testStaticQueryResolving() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        ImmutableList<KeYJavaType> signature =
                ImmutableSLList.<KeYJavaType>nil();

        IProgramMethod pm = javaInfo.getProgramMethod(testClassType,
                                                     "staticMethod", signature,
                                                     testClassType);

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "testPackage.TestClass.staticMethod() == 4"), testClassType,
                    selfVar,
                    null, null, null, null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);
        assertTrue(result.sub(0).op().equals(pm));
    }


    public void testSubtypeExpression() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();

        try {
            result = JMLTranslator.translate(
                    new PositionedString(
                    "( \\exists TestClass t; t != null; \\typeof(t) <: \\type(java.lang.Object) )"),
                    testClassType, selfVar,
                    null, null, null, null, JavaDLTerm.class, services);
        } catch (SLTranslationException e) {
            e.printStackTrace();
            assertTrue(false);
        }

        assertTrue(result != null);

        Sort sds = javaInfo.objectSort();
        Function ioFunc = sds.getInstanceofSymbol(services);
        assertTrue(termContains(result, ioFunc));
    }


    public void testCorrectImplicitThisResolution() {
        JavaDLTerm result = null;

        ProgramVariable selfVar = buildSelfVarAsProgVar();
        LocationVariable array = (LocationVariable) javaInfo.getAttribute(
                "testPackage.TestClass::array");

        try {
            result = JMLTranslator.translate(new PositionedString(
                    "(\\forall TestClass a;a.array == array; a == this)"),
                                                    testClassType,
                                                    selfVar,
                                                    null,
                                                    null,
                                                    null,
                                                    null,
                                                    JavaDLTerm.class,
                                                    services);
        } catch (SLTranslationException e) {
            assertTrue("Parsing Error: " + e, false);
        }

        assertTrue(result != null);
        final LogicVariable qv =
                new LogicVariable(new Name("a"), selfVar.sort());
        final Function fieldSymbol = services.getTheories().getHeapLDT().getFieldSymbolForPV(
                array, services);
        JavaDLTerm expected = TB.all(qv,
                               TB.imp(
                TB.and(TB.and(TB.equals(TB.dot(array.sort(),
                                               TB.var(qv),
                                               fieldSymbol),
                                        TB.dot(array.sort(),
                                               TB.var(selfVar),
                                               fieldSymbol)),
                              TB.reachableValue(TB.var(qv),
                                                selfVar.getKeYJavaType())),
                       TB.not(TB.equals(TB.var(qv),
                                        TB.NULL()))), // implicit non null
                                      TB.equals(TB.var(qv), TB.var(selfVar))));        
                
        assertTrue("Expected:" + ProofSaver.printTerm(expected, services)
                   + "\n Was:" + ProofSaver.printTerm(result, services),
                   result.equalsModRenaming(expected));
    }
}