/* package de.uka.ilkd.key.loopinvgen;

import java.util.Set;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

public class PredicateRefinement {

	public Set<Term> depList;
	public Set<ComparativeOperator> compList;
	private Semisequent ante;
	private final Goal goal;
	private final Services services;
	private final Name noRAW, noWAR, noWAW, noW, noR;

	public PredicateRefinement(Goal g, Set<ComparativeOperator> compPredList, Set<Term> depPredList) {
		goal = g;
		services = goal.proof().getServices();
		compList = compPredList;
		depList = depPredList;
		ante = goal.sequent().antecedent();

	}

	public void antecedentPredicate() {
		for (SequentFormula sf : ante) {
			if (sf.formula().op() instanceof ComparativeOperator) {
				delCompPred((ComparativeOperator) sf.formula().op());
				
			} else if (sf.formula().op().name().equals(noRAW) || sf.formula().op().name().equals(noWAR)
					|| sf.formula().op().name().equals(noWAW) || sf.formula().op().name().equals(noR)
					|| sf.formula().op().name().equals(noW)) {
				delDepPred(sf);
			}
		}
	}

	private void delCompPred(ComparativeOperator cp) {
		ExtList children = new ExtList();
		children.add((Object) cp.getChildAt(0));
		children.add((Object) cp.getChildAt(1));

		Equals eq = new Equals(children);
		GreaterThan gt = new GreaterThan(children);
		GreaterOrEquals goe = new GreaterOrEquals(children);
		LessThan lt = new LessThan(children);
		LessOrEquals loe = new LessOrEquals(children);

		if (cp instanceof Equals) {
			compList.remove(gt);
			compList.remove(lt);
		} else if (cp instanceof GreaterThan) {
			compList.remove(lt);
			compList.remove(loe);
			compList.remove(eq);
		}

		else if (cp instanceof GreaterOrEquals) {
			compList.remove(lt);
		}

		else if (cp instanceof LessThan) {
			compList.remove(gt);
			compList.remove(goe);
			compList.remove(eq);
		}

		else if (cp instanceof LessOrEquals) {
			compList.remove(gt);
		}
	}

	private void delDepPred(SequentFormula sf) {
		Name name = sf.formula().op().name();
//		Term t = ((Term)sf).sub(0);
		System.out.println(((Term)sf).sub(0).sort());
		//TODO
	}
}

    
*/