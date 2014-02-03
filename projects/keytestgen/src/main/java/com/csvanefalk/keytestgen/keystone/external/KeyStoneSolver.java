/**
 *
 */
package com.csvanefalk.keytestgen.keystone.external;

import com.csvanefalk.keytestgen.core.model.ModelGeneratorException;
import com.csvanefalk.keytestgen.keystone.KeYStone;
import com.csvanefalk.keytestgen.keystone.KeYStoneException;
import com.csvanefalk.keytestgen.util.transformers.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Huy Do
 */
public class KeyStoneSolver extends FormulaSolver {
    private Services services;


    /**
     * @param formula
     * @param service
     */
    public KeyStoneSolver(Term formula, Services services) {
        super(formula);
        this.services = services;
        // TODO Auto-generated constructor stub
    }

    /*
     * solve formula by using KeYStone, a solver developed and used in keytestgen2
     */
    public Map<String, Integer> solveFormula() {
      /*
       * Bring the pathcondition into a simplified form suitable for model generation.
       */
        Term t1;
        try {
            t1 = configurePathConditionForModelGeneration(formula);
        } catch (TermTransformerException e) {
            t1 = formula;
        }
        //t1=formula;
        System.out.println("t1:" + t1.toString());
           /*
       * Complete the model with concrete integer values.
       */
        Map<String, Integer> concreteValues = new HashMap<String, Integer>();
        try {
            concreteValues = getConcreteValues(t1, services);
        } catch (Exception e) {
            System.out.println("error happen in getConcreteValues pharse");
            e.printStackTrace();
        }
        return concreteValues;
    }

    private Term configurePathConditionForModelGeneration(Term pathCondition) throws TermTransformerException {

      /*
       * Remove all axiomatic expressions
       */
        pathCondition = RemoveAxiomaticExpressionsTransformer.getInstance().transform(pathCondition);

      /*
       * Remove all implications from the path condition.
       */
        pathCondition = RemoveImplicationsTransformer.getInstance().transform(pathCondition);

      /*
       * Remove if-then-else assertions from the path condition.
       */
        pathCondition = RemoveIfThenElseTransformer.getInstance().transform(pathCondition);

        return pathCondition;
    }

    private Map<String, Integer> getConcreteValues(final Term pathCondition,
                                                   Services services) throws ModelGeneratorException {
        try {
            Term simplifiedPathCondition = configurePathConditionForIntegerGeneration(pathCondition, services);

            Map<String, Integer> result;
            if (simplifiedPathCondition == null) {
                result = new HashMap<String, Integer>();
            } else {
                KeYStone keYStone = KeYStone.getInstance();
                result = keYStone.solveConstraint(simplifiedPathCondition);
            }
         /*
         PaperTest.addResult(pathCondition + "_KEYSTONE",
         Calendar.getInstance().getTimeInMillis() - time);
         */
            return result;

        } catch (final TermTransformerException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (final KeYStoneException e) {
            throw new ModelGeneratorException(e.getMessage());
        } catch (NullPointerException e) {
            System.out.println("null pointer exception!");
            e.printStackTrace();
        }
        return null;
    }

    /**
     * Configures a path condition for generating concrete integer values.
     *
     * @param pathCondition
     * @return
     */
    private Term configurePathConditionForIntegerGeneration(Term pathCondition,
                                                            Services services) throws TermTransformerException {

        pathCondition = RemoveObserverFunctionsTransformer.getInstance().transform(pathCondition);

        pathCondition = TermSimplificationTransformer.getInstance().transform(pathCondition);

        pathCondition = NormalizeArithmeticComparatorsTransformer.getInstance(services)
                                                                 .transform(pathCondition);

        return pathCondition;
    }
}
