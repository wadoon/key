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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * TODO: rewrite, this seems pretty inefficient ...
 */
public class PredictCostProver {

    private final TermBuilder tb;

    private final Term trueT, falseT;

    /** assume that all literal in <code>assertLiterals</code> are true */
    private Set<Term> assertLiterals;
    
    /** clauses from <code>instance</code> of CNF */
    private Set<Clause> clauses = new LinkedHashSet<Clause>();

    private final Services services;

    private PredictCostProver(Term instance, Set<Term> p_assertList,
	    Services services) {
	this.assertLiterals = p_assertList;
	this.services = services;
	this.tb = services.getTermBuilder(); 
	this.trueT = tb.tt();
	this.falseT = tb.ff();
	initClauses(instance);
    }

    public static long computerInstanceCost(Substitution sub, Term matrix,
	    Set<Term> assertList, Services services) {

	if (!sub.isGround()) {
	    // non-ground substitutions not supported yet
	    return -1;
	} else {
	    Set<Term> assertions;
	    if (assertList instanceof HashSet) {
	        assertions = (Set<Term>) ((HashSet) assertList).clone();
	    } else {
	        assertions = new HashSet<Term>();
	        assertions.addAll(assertList);
	    }
	        
	    final PredictCostProver prover = new PredictCostProver(sub
		.applyWithoutCasts(matrix, services), assertions, services);
	    return prover.cost();
	}
    }

    // init context
    private void initClauses(Term instance) {
        for (final Term t : TriggerUtils.setByOperator(instance, Junctor.AND)) {
            clauses.add(new Clause(TriggerUtils.setByOperator(t, Junctor.OR)));
        }
    }

    // end

    
    // (2)self-proved rule
    /**
     * If the given <code>problem</code>'s operation is equal,or mathematics
     * operation(=,>=, <=), this method will try to prove it by finding the
     * relation between its two subterms.
     */
    private Term provedBySelf(Term p_problem) {
        final Term problem = TriggerUtils.discardDoubleNegation(p_problem);        
        final boolean negated = (problem.op() == Junctor.NOT); 
        final Term pro = (negated ? problem.sub(0) : problem);
        
        if ((pro.op() == Equality.EQUALS || pro.op() == Equality.EQV) && 
                pro.sub(0).equalsModRenaming(pro.sub(1)))
            return negated ? falseT : trueT;
        
        final Term arithRes = HandleArith.provedByArith(pro, services);
        if (TriggerUtils.isTrueOrFalse(arithRes))           
                return negated ? tb.not(arithRes) : arithRes;
            else
                return arithRes;
    }

    // (3)equal rule
    /***
     * @return trueT if problem is equal axiom, false if problem's negation is
     *         equal axiom. Otherwise retrun problem.
     */
    private Term directConsequenceOrContradictionOfAxiom(Term problem, Term axiom) {
        Term strippedProblem = TriggerUtils.discardDoubleNegation(problem);
        Term strippedAxiom   = TriggerUtils.discardDoubleNegation(axiom);		
        boolean negated = false; 

        if (strippedProblem.op() != strippedAxiom.op()) {
            if (strippedProblem.op() == Junctor.NOT) {
                strippedProblem = strippedProblem.sub(0);
                negated = true;
            } else if (strippedAxiom.op() == Junctor.NOT) {
                strippedAxiom = strippedAxiom.sub(0);	        
                negated = true;
            } else {
                return problem;
            }        
        }	

        if (strippedProblem.equalsModRenaming(strippedAxiom)) {
            return negated ? falseT : trueT;
        }
        return problem;
    }

    // (4)combine provedByequal and provedByArith .
    /**
     * @param problem
     * @param axiom
     * @return if axiom conduct problem then return trueT. If axiom conduct
     *         negation of problem return fastT. Otherwise, return problem
     */
    private Term provedByAnother(Term problem, Term axiom) {
	Term res = directConsequenceOrContradictionOfAxiom(problem, axiom);
	if (TriggerUtils.isTrueOrFalse(res))
	    return res;
	return HandleArith.provedByArith(problem, axiom, services);
    }

    // (5) combine rules
    /**
     * try to prove <code>problem</code> by know <code>assertLits</code>
     * 
     * @param problem
     *            a literal to be proved
     * @param assertLits
     *            a set of term assertLiterals in which all literals are true
     * @return return <code>trueT</code> if if formu is proved to true,
     *         <code> falseT</code> if false, and <code>atom</code> if it cann't
     *         be proved.
     */
    private Term proveLiteral(Term problem, Set<? extends Term> assertLits) {
        Term res = provedBySelf(problem);
        if (TriggerUtils.isTrueOrFalse(res)) {
            return res;
        }
        
        for (Term t : assertLits) {
            res = provedByAnother(problem, t);
            if (TriggerUtils.isTrueOrFalse(res)) {
                return res;
            }
        }
        return problem;
    }

    
    
   
    // end

    // cost computation

    /**
     * refine every clause, by assume assertList are true and if a clause's cost
     * is 0 which means it is refined to false, then cost 0 returned. If every
     * clause's cost is -1 which means every clause is refined to true, cost -1
     * returned. Otherwise, multiply of every cost is return. Beside, if a
     * clause is refined to a situation that only one literal is left, the
     * literal will be add to assertLiterals.
     */
    private long cost() {
        long cost = 1;
        boolean assertChanged = false;
        final Set<Clause> res = new LinkedHashSet<Clause>();
        clauseLoop:
            for (final Clause c : clauses) {
                c.refine(assertLiterals);
                final int cCost = c.cost();
                switch (cCost) {
                case 0:
                    clauses.clear();
                    return 0;
                case -1:
                    continue clauseLoop;
                }
                if (c.literals.size() == 1) {
                    assertChanged = true;
                    assertLiterals.addAll(c.literals);
                } else {
                    res.add(c);
                }	
                cost = cost * cCost;
            }
        clauses = res;
        if (!assertChanged && res.isEmpty())
            return -1;
        return cost;
    }

    private class Clause {

	/** all literals contains in this clause */
	public Set<Term> literals;

	
	public Clause(Set<Term> lits) {
	    literals = lits;
	}	
	
	public boolean equals(Object o) {
	    if (!(o instanceof Clause)) return false;
	    final Clause other = (Clause) o;
	    if (other.literals.size() != literals.size()) {
		return false;
	    }
	    return literals.equals(other.literals);
	}
	
	public int hashCode() {
	    return literals.hashCode();
	}


	/**
	 * @return 0 if this clause is refine to false. -1 if true.
	 *         Otherwise,return the number of literals it left.
	 */
	public int cost() {
	    if (literals.size() == 1 && literals.contains(falseT))
		return 0;
	    if (literals.contains(trueT))
		return -1;
	    return literals.size();
	}

	/**
	 * Refine literals in this clause, but it does not change literlas, only
	 * return literals that can't be removed by refining
	 */
	public void refine(final Set<? extends Term> assertLits) {
	    final Set<Term> res = new HashSet<>();
	    for (final Term lit : literals) {
	        final Operator op = proveLiteral(lit, assertLits).op();
	        if (op == Junctor.TRUE) {
	            res.clear();
	            res.add(trueT);
	            break;
	        }
	        if (op == Junctor.FALSE) {
	            continue;
	        }
	        res.add(lit);
	    }
	    if (res.size() == 0)
	        res.add(falseT);
	    literals = res;
	}

	public String toString() {
	    return literals.toString();
	}
    }

}