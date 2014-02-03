/**
 *
 */
package com.csvanefalk.keytestgen.keystone.external;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

import java.util.Map;

/**
 * This class solves the formula represented by a Term object.
 *
 * @author Huy Do
 */
public abstract class FormulaSolver {
    protected Term formula;

    /**
     * @param formula
     */
    public FormulaSolver(Term formula) {
        super();
        this.formula = formula;
    }

    /**
     * @param formula
     * @param service
     */
    public FormulaSolver(Term formula, Services service) {
        super();
        this.formula = formula;
    }

    /**
     * @return the formula
     */
    public Term getFormula() {
        return formula;
    }

    /**
     * @param formula the formula to set
     */
    public void setFormula(Term formula) {
        this.formula = formula;
    }

    /*
     * this method should be rewritten in subclass
     * */
    public abstract Map<String, Integer> solveFormula();

    //to do: implement another method to solve formula (using SMTSolver)
}
