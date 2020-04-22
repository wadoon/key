// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.abstractexecution;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.util.collection.UniqueArrayList;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.AbstractTestTermParser;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.merge.MergeRuleTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

/**
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateTests extends AbstractTestTermParser {
    private static final File TEST_RESOURCES_DIR_PREFIX = new File(
            HelperClassForTests.TESTCASE_DIRECTORY, "abstractexecution/abstractupdates/");

    private static Services DUMMY_SERVICES;
    private static Proof DUMMY_PROOF;
    private static Sort INT_SORT;
    private static TermBuilder TB;

    // /////////////////////////////////// //
    // ////////////// SETUP ////////////// //
    // /////////////////////////////////// //

    @BeforeClass
    public static void prepare() throws ProblemLoaderException {
        final KeYEnvironment<DefaultUserInterfaceControl> env = //
                HelperClassForTests.createKeYEnvironment();
        DUMMY_SERVICES = env.getServices();
        DUMMY_PROOF = DUMMY_SERVICES.getProof();
        INT_SORT = DUMMY_SERVICES.getNamespaces().sorts().lookup("int");
        TB = DUMMY_SERVICES.getTermBuilder();
    }

    @Before
    public void setUp() throws RecognitionException {
        parseDecls("\\programVariables {" //
                + "byte[] newObject;" //
                + "byte[] arr;" //
                + "}" //
                + "\\functions {" //
                + "\\unique LocSet locset1;" //
                + "\\unique LocSet locset2;" //
                + "}");
    }

    // /////////////////////////////////// //
    // ////////////// TESTS ////////////// //
    // /////////////////////////////////// //

    //@formatter:off
    //    {U_P(w:=x)}
    //      {U_Q(y:=z)}p(w,x,y,z)
    //<-> {U_Q(y:=z)}
    //      {U_P(w:=x)}p(w,x,y,z)
    //@formatter:on
    @Test
    public void reorderIndependentAbstractUpdates()
            throws ProblemLoaderException, ProofInputException {
        final LocationVariable lvW = intVar("w");
        final LocationVariable lvX = intVar("x");
        final LocationVariable lvY = intVar("y");
        final LocationVariable lvZ = intVar("z");

        final Term u1 = abstractUpdate(aps("P"), new PVLoc(lvW), TB.var(lvX));
        final Term u2 = abstractUpdate(aps("Q"), new PVLoc(lvY), TB.var(lvZ));

        final Term pred = TB.func(
                new Function(new Name("p"), Sort.FORMULA, INT_SORT, INT_SORT, INT_SORT, INT_SORT),
                TB.var(lvW), TB.var(lvX), TB.var(lvY), TB.var(lvZ));

        final Term equivalence = TB.equals(TB.apply(u1, TB.apply(u2, pred)),
                TB.apply(u2, TB.apply(u1, pred)));

        final Proof proof = startProofFor(equivalence);
        assertEquals(true, proof.closed());
    }

    @Test
    public void skolemLocValConversion() throws ProofInputException {
        final LocSetLDT locSetLDT = DUMMY_SERVICES.getTypeConverter().getLocSetLDT();
        final Sort locSetSort = locSetLDT.targetSort();
        final Function valueFun = locSetLDT.getValue();

        final Function abstractLocSetFun = //
                new Function(new Name("abstrLocSet"), locSetSort, false, true, new Sort[0]);
        final LocationVariable x = intVar("x");

        final Term xAssignedOne = TB.elementary(TB.var(x), TB.one());
        final Term abstrLocSetTerm = TB.func(abstractLocSetFun);
        final Term valOfAbstrLocSet = TB.func(valueFun, abstrLocSetTerm);

        // Provable: {x:=1}abstrLocSet = abstrLocSet
        final Term equivalenceOne = //
                TB.equals(TB.apply(xAssignedOne, abstrLocSetTerm), abstrLocSetTerm);

        final Proof proofOne = startProofFor(equivalenceOne);
        assertTrue(proofOne.closed());

        // NOT Provable: {x:=1}value(abstrLocSet) = value(abstrLocSet)
        final Term equivalenceTwo = //
                TB.equals(TB.apply(xAssignedOne, valOfAbstrLocSet), valOfAbstrLocSet);

        final Proof proofTwo = startProofFor(equivalenceTwo);
        assertFalse(proofTwo.closed());
    }

    @Test
    public void updatesInFrontOfLocsetTerms() throws Exception {
        final Term arrayRangeEquiv = parseFormula(
                "{newObject:=arr}arrayRange(newObject,0,-1+newObject.length)="
                        + "arrayRange(arr,0,-1+arr.length)");
        final Proof arrayRangeEquivProof = startProofFor(arrayRangeEquiv);
        assertTrue(arrayRangeEquivProof.closed());

        final Term locsetCapEquiv = parseFormula(
                "{newObject:=arr}(disjoint(locset1,locset2))<->disjoint(locset1,locset2)");
        final Proof locsetCapEquivProof = startProofFor(locsetCapEquiv);
        assertTrue(locsetCapEquivProof.closed());
    }

    @Test
    public void simplificationTests() {
        final Map<String, Boolean> simplificationTests = new LinkedHashMap<>();
        simplificationTests.put("simplificationTest01.key", true);
        simplificationTests.put("simplificationTest02.key", true);
        simplificationTests.put("simplificationTest03-INCORR.key", false);
        simplificationTests.put("simplificationTest04.key", true);
        simplificationTests.put("simplificationTest05-INCORR.key", false);
        simplificationTests.put("simplificationTest06.key", true);
        simplificationTests.put("simplificationTest07.key", true);
        simplificationTests.put("simplificationTest08-INCORR.key", false);
        simplificationTests.put("simplificationTest09-INCORR.key", false);
        simplificationTests.put("simplificationTest10.key", true);
        simplificationTests.put("simplificationTest11.key", true);
        simplificationTests.put("simplificationTest12-INCORR.key", false);
        simplificationTests.put("simplificationTest13.key", true);
        simplificationTests.put("simplificationTest14-INCORR.key", false);
        simplificationTests.put("simplificationTest15.key", true);
        simplificationTests.put("simplificationTest16.key", true);
        simplificationTests.put("simplificationTest17-INCORR.key", false);
        simplificationTests.put("simplificationTest18.key", true);
        simplificationTests.put("simplificationTest19-INCORR.key", false);
        simplificationTests.put("simplificationTest20.key", true);
        simplificationTests.put("simplificationTest21-INCORR.key", false);
        simplificationTests.put("simplificationTest22.key", true);
        simplificationTests.put("simplificationTest23-INCORR.key", false);
        simplificationTests.put("simplificationTest24.key", true);
        simplificationTests.put("simplificationTest25-INCORR.key", false);
        simplificationTests.put("simplificationTest26-INCORR.key", false);
        simplificationTests.put("simplificationTest27.key", true);

        for (final String keyFile : simplificationTests.keySet()) {
            final Proof proof = MergeRuleTests.loadProof(TEST_RESOURCES_DIR_PREFIX, keyFile);
            MergeRuleTests.startAutomaticStrategy(proof, 10000);

            assertEquals("Failed " + keyFile, simplificationTests.get(keyFile), proof.closed());
        }
    }

    // //////////////////////////////////////////// //
    // ////////////// HELPER METHODS ////////////// //
    // //////////////////////////////////////////// //

    private Proof startProofFor(Term formula) throws ProofInputException {
        final ProofEnvironment proofEnv = SideProofUtil
                .cloneProofEnvironmentWithOwnOneStepSimplifier(DUMMY_PROOF);
        final ProofStarter proofStarter = SideProofUtil.createSideProof(proofEnv,
                Sequent.createSuccSequent(new Semisequent(new SequentFormula(formula))), "test");
        final ApplyStrategyInfo applInfo = proofStarter.start();
        return applInfo.getProof();
    }

    private AbstractStatement aps(String id) {
        return new AbstractStatement(id);
    }

    private Term abstractUpdate(AbstractStatement aps, AbstractUpdateLoc lhs, Term rhs) {
        return abstractUpdate(aps, new AbstractUpdateLoc[] { lhs }, new Term[] { rhs });
    }

    private Term abstractUpdate(AbstractStatement aps, AbstractUpdateLoc[] lhs, Term[] rhs) {
        final TermBuilder tb = DUMMY_SERVICES.getTermBuilder();

        final AbstractUpdateFactory abstrUpdF = DUMMY_SERVICES.abstractUpdateFactory();

        final UniqueArrayList<AbstractUpdateLoc> lhsLocs = Arrays.stream(lhs)
                .collect(Collectors.toCollection(() -> new UniqueArrayList<>()));

        final AbstractUpdate upd = //
                abstrUpdF.getInstance(aps, lhsLocs, rhs.length);
        return tb.abstractUpdate(upd, rhs);
    }

    private LocationVariable intVar(final String name) {
        return new LocationVariable(new ProgramElementName(name),
                DUMMY_SERVICES.getNamespaces().sorts().lookup("int"));
    }

}
