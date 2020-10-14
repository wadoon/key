package de.uka.ilkd.key.loopinvgen;

import java.util.ArrayList;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.expression.operator.ComparativeOperator;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;

public class ConstructAllCompPreds {

	private int low, idx, high;

	public ConstructAllCompPreds(int low, int index, int high) {
		this.low = low;
		this.idx = index;
		this.high = high;

	}

	private ArrayList<ComparativeOperator> consCompPreds(int lh, int rh) {
		ArrayList<ComparativeOperator> compPredList = new ArrayList<ComparativeOperator>();

		ExtList input = new ExtList();
		input.add((Object) lh);
		input.add((Object) rh);

		GreaterOrEquals goe = new GreaterOrEquals(input);
		compPredList.add(goe);

		GreaterThan gt = new GreaterThan(input);
		compPredList.add(gt);

		LessOrEquals loe = new LessOrEquals(input);
		compPredList.add(loe);

		LessThan lt = new LessThan(input);
		compPredList.add(lt);

		Equals eq = new Equals(input);
		compPredList.add(eq);

		return compPredList;
	}

	public ArrayList<ComparativeOperator> consAllCompPreds() {
		ArrayList<ComparativeOperator> compPredList = new ArrayList<ComparativeOperator>();

		compPredList.addAll(consCompPreds(this.low, this.idx));
		compPredList.addAll(consCompPreds(this.low, this.high));
		compPredList.addAll(consCompPreds(this.idx, this.high));

		return compPredList;
	}
}
