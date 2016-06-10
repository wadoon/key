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

package de.uka.ilkd.key.symbolic_execution.testcase.util;

import java.io.File;
import java.util.HashMap;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Sort;
import org.key_project.common.core.logic.op.LogicVariable;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.testcase.AbstractSymbolicExecutionTestCase;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Tests for {@link SymbolicExecutionUtil}
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionUtil extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests {@link SymbolicExecutionUtil#improveReadability(de.uka.ilkd.key.logic.JavaDLTerm)}
    */
   public void testImproveReadability() throws ProblemLoaderException {
      KeYEnvironment<?> environment = KeYEnvironment.load(new File(testCaseDirectory, "/readability/InnerAndAnonymousTypeTest.java"), null, null, null);
      Services services = environment.getServices();
      IntegerLDT integerLDT = services.getTheories().getIntegerLDT();
      Sort intSort = integerLDT.targetSort();
      final TermBuilder TB = services.getTermBuilder();
      // Create test terms
      JavaDLTerm a = TB.var(new LogicVariable(new Name("a"), intSort));
      JavaDLTerm b = TB.var(new LogicVariable(new Name("b"), intSort));
      JavaDLTerm aleqb = TB.leq(a, b);
      JavaDLTerm altb = TB.lt(a, b);
      JavaDLTerm agtb = TB.gt(a, b);
      JavaDLTerm ageqb = TB.geq(a, b);
      JavaDLTerm notAleqb = TB.not(aleqb);
      JavaDLTerm notAltb = TB.not(altb);
      JavaDLTerm notAgtb = TB.not(agtb);
      JavaDLTerm notAgeqb = TB.not(ageqb);
      JavaDLTerm onePlusB = TB.add(TB.one(), b);
      JavaDLTerm bPlusOne = TB.add(b, TB.one());
      JavaDLTerm altOnePlusB = TB.lt(a, onePlusB);
      JavaDLTerm altBPlusOne = TB.lt(a, bPlusOne);
      JavaDLTerm ageqOnePlusB = TB.geq(a, onePlusB);
      JavaDLTerm ageqBPlusOne = TB.geq(a, bPlusOne);
      JavaDLTerm minusOne = services.getTheories().getIntegerLDT().translateLiteral(new IntLiteral(-1), services);
      JavaDLTerm minusOnePlusB = TB.add(minusOne, b);
      JavaDLTerm bPlusMinusOne = TB.add(b, minusOne);
      JavaDLTerm bMinusOne = TB.func(integerLDT.getSub(), b, TB.one());
      JavaDLTerm aleqMinusOnePlusB = TB.leq(a, minusOnePlusB);
      JavaDLTerm aleqBPlusMinusOne = TB.leq(a, bPlusMinusOne);
      JavaDLTerm aleqBMinusOne = TB.leq(a, bMinusOne);
      JavaDLTerm agtMinusOnePlusB = TB.gt(a, minusOnePlusB);
      JavaDLTerm agtBPlusMinusOne = TB.gt(a, bPlusMinusOne);
      JavaDLTerm agtBMinusOne = TB.gt(a, bMinusOne);
      // Test null
      assertNull(SymbolicExecutionUtil.improveReadability(null, services));
      assertTerm(notAleqb, SymbolicExecutionUtil.improveReadability(notAleqb, null));
      // Test simple ! <, ! <=, ! >, ! >= improvements
      assertTerm(agtb, SymbolicExecutionUtil.improveReadability(notAleqb, services));
      assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(notAltb, services));
      assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(notAgtb, services));
      assertTerm(altb, SymbolicExecutionUtil.improveReadability(notAgeqb, services));
      // Test < 1 +, < + 1
      assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(altOnePlusB, services));
      assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(altBPlusOne, services));
      // Test >= 1 +, >= + 1
      assertTerm(agtb, SymbolicExecutionUtil.improveReadability(ageqOnePlusB, services));
      assertTerm(agtb, SymbolicExecutionUtil.improveReadability(ageqBPlusOne, services));
      // Test <= -1 +, <= + -1
      assertTerm(altb, SymbolicExecutionUtil.improveReadability(aleqMinusOnePlusB, services));
      assertTerm(altb, SymbolicExecutionUtil.improveReadability(aleqBPlusMinusOne, services));
      assertTerm(altb, SymbolicExecutionUtil.improveReadability(aleqBMinusOne, services));
      // Test > -1 +, > + -1
      assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(agtMinusOnePlusB, services));
      assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(agtBPlusMinusOne, services));
      assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(agtBMinusOne, services));
      // Test combined
      assertTerm(agtb, SymbolicExecutionUtil.improveReadability(TB.not(altOnePlusB), services));
      assertTerm(aleqb, SymbolicExecutionUtil.improveReadability(TB.not(ageqOnePlusB), services));
      assertTerm(ageqb, SymbolicExecutionUtil.improveReadability(TB.not(aleqBPlusMinusOne), services));
      assertTerm(altb, SymbolicExecutionUtil.improveReadability(TB.not(agtBMinusOne), services));
      // Test complex term
      JavaDLTerm complex = TB.and(altOnePlusB,
                            TB.or(ageqBPlusOne, agtMinusOnePlusB));
      JavaDLTerm expectedComplex = TB.and(aleqb,
                                    TB.or(agtb, ageqb));
      assertTerm(expectedComplex, SymbolicExecutionUtil.improveReadability(complex, services));
      environment.dispose();
   }

   /**
    * Tests {@link SymbolicExecutionUtil#getChoiceSetting(String)} and
    * {@link SymbolicExecutionUtil#setChoiceSetting(String, String)} and
    * {@link SymbolicExecutionUtil#isChoiceSettingInitialised()}.
    */
   public void testGetAndSetChoiceSetting() throws Exception {
      String originalValue = null; 
      try {
         assertTrue(SymbolicExecutionUtil.isChoiceSettingInitialised());
         // Store default choice settings
         HashMap<String, String> defaultSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         assertFalse(defaultSettings.isEmpty());
         // Test initial value
         originalValue = SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS);
         assertTrue(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW.equals(originalValue) || SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN.equals(originalValue));
         // Change value and make sure that it has changed
         String newValue = SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW.equals(originalValue) ? SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN : SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW; 
         SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
         assertEquals(newValue, SymbolicExecutionUtil.getChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS));
         // Make sure that all other settings are unchanged.
         HashMap<String, String> changedSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
         defaultSettings.put(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, newValue);
         assertEquals(defaultSettings, changedSettings);
      }
      finally {
         if (originalValue != null) {
            SymbolicExecutionUtil.setChoiceSetting(SymbolicExecutionUtil.CHOICE_SETTING_RUNTIME_EXCEPTIONS, originalValue);
         }
      }
   }
}