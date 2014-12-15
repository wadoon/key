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

/** 
 * Created on: May 18, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.List;
import java.util.LinkedList;
import java.util.Collections;
import de.uka.ilkd.key.ldt.FloatLDT;


public class SMTTermFloatOp extends SMTTerm{

	private static SMTSort ROUNDMODESORT = new SMTSort("RoundingMode");

	public static class Op {

		public static Op FPNEG	    = new Op("fp.neg", SMTSort.FLOAT, SMTSort.FLOAT);
		public static Op FPISNAN    = new Op("fp.isNaN", SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPISNORMAL = new Op("fp.isNormal", SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPLT	    = new Op("fp.lt", SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPGT	    = new Op("fp.gt", SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPLEQ	    = new Op("fp.leq", SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPGEQ	    = new Op("fp.geq", SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPEQ	    = new Op("fp.eq", SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.BOOL);
		public static Op FPADD	    = new Op("fp.add", ROUNDMODESORT, SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.FLOAT);
		public static Op FPSUB	    = new Op("fp.sub", ROUNDMODESORT, SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.FLOAT);
		public static Op FPMUL	    = new Op("fp.mul", ROUNDMODESORT, SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.FLOAT);
		public static Op FPDIV	    = new Op("fp.div", ROUNDMODESORT, SMTSort.FLOAT, SMTSort.FLOAT, SMTSort.FLOAT);

		public static Op CASTLONGTOFLOAT  = new Op("(_ to_fp 8 24) RNE", SMTSort.INT, SMTSort.FLOAT);
		public static Op CASTFLOATTOLONG  = new Op("(_ fp.to_sbv 64) RTZ", SMTSort.FLOAT, SMTSort.INT);


		private final int arity;
		private final String op;
		private final List<SMTSort> domainSorts;
		private final SMTSort imageSort;

		public Op(String op, SMTSort... sorts) {
			if (sorts.length < 1) {
				throw new IllegalArgumentException(
				    "At least one argument sort is needed, the image sort.");
			}
			this.arity = sorts.length - 1;
			this.op = op;
			this.domainSorts = new LinkedList<SMTSort>();

			for (int i = 0; i < this.arity; i++) {
				this.domainSorts.add(sorts[i]);
			}
			this.imageSort = sorts[sorts.length - 1];
		}

		public String getOpName() {
			return op;
		}

		@Override
		public boolean equals (Object other) {
			if (other == null)
				return false;
			
			if (this == other)
				return true;
			
			if (!(other instanceof Op))
				return false;
			Op otherop = (Op) other;
			
			return this.op.equals(otherop.op) &&
				this.arity == otherop.arity &&
				this.domainSorts.equals(otherop.domainSorts) &&
				this.imageSort.equals(otherop.imageSort);
		}
	}


	private Op operator;
	private List<SMTTerm> subs;
		
	/**
	 * @param operator
	 * @param sub
	 */
	public SMTTermFloatOp(Op operator, List<SMTTerm> subs) {
		super();
		this.operator = operator;
		this.subs = subs;
	}
	
	
	/**
	 * @return the operator
	 */
	public Op getOperator() {
		return operator;
	}
	/**
	 * @param operator the operator to set
	 */
	public void setOperator(Op operator) {
		this.operator = operator;
	}


	@Override
	public List<SMTTerm> getSubs() {
		return subs;
	}


	public void setSubs(List<SMTTerm> subs) {
		this.subs = subs;
	}

	
	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getQuantVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		for(int i = 0; i< subs.size(); i++){
			vars.addAll(subs.get(i).getQuantVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getUQVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		for(int i = 0; i< subs.size(); i++){
			vars.addAll(subs.get(i).getUQVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getEQVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();
		for(int i = 0; i< subs.size(); i++){
			vars.addAll(subs.get(i).getEQVars());
		}
		return vars;
	}

	/** {@inheritDoc} */
	@Override
	public List<SMTTermVariable> getVars() {
		List<SMTTermVariable> vars = new LinkedList<SMTTermVariable>();

		for(int i = 0; i< subs.size(); i++){
			vars.addAll(subs.get(i).getVars());
		}
		return vars;
	}
	
	

	/** {@inheritDoc} */
	@Override
	public boolean occurs (SMTTermVariable a) {
		for(int i = 0; i < subs.size(); i++){
			if(subs.get(i).occurs(a))
				return true;
		}
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public boolean occurs (String id) {	
		for(int i = 0; i < subs.size(); i++){
			if(subs.get(i).occurs(id))
				return true;
		}
		return false;
	}

	/** {@inheritDoc} */
	@Override
	public SMTSort sort () {
		return operator.imageSort;
	}
	

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTermVariable a, SMTTerm b) {		

		if (subs.isEmpty())
			return this;

		LinkedList<SMTTerm> newSubs = new LinkedList<SMTTerm>();		
		for(SMTTerm sub : subs){
			newSubs.add(sub.substitute(a, b));
		}
		return new SMTTermFloatOp(operator, newSubs);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm substitute (SMTTerm a, SMTTerm b) {
		if (subs.isEmpty())
			return this;

		if (this.equals(a))
			return b;

		LinkedList<SMTTerm> newSubs = new LinkedList<SMTTerm>();
		for(SMTTerm sub : subs){
			newSubs.add(sub.substitute(a, b));
		}
		return new SMTTermFloatOp(operator, newSubs);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm replace (SMTTermCall a, SMTTerm b) {
		if (subs.isEmpty())
			return this;

		LinkedList<SMTTerm> newSubs = new LinkedList<SMTTerm>();
		for(SMTTerm sub : subs){
			newSubs.add(sub.replace(a, b));
		}
		return new SMTTermFloatOp(operator, newSubs);
	}

	/** {@inheritDoc} */
	@Override
	public SMTTerm instantiate (SMTTermVariable a, SMTTerm b) {

		if (subs.isEmpty())
			return this;

		LinkedList<SMTTerm> newSubs = new LinkedList<SMTTerm>();
		for(SMTTerm sub : subs){
			newSubs.add(sub.instantiate(a, b));
		}
		return new SMTTermFloatOp(operator, newSubs);
	}

	@Override
	public SMTTermFloatOp copy () {

		List<SMTTerm> newSubs = new LinkedList<SMTTerm>();
		for(SMTTerm t : subs){
			newSubs.add(t.copy());
		}


		return new SMTTermFloatOp(this.operator, newSubs);
	}
	
	@Override
	public boolean equals (Object term) {
		if (term == null)
			return false;
		
		if (this == term)
			return true;
		
		if (!(term instanceof SMTTermFloatOp))
			return false;
		SMTTermFloatOp ut = (SMTTermFloatOp) term;
		
		return this.operator.equals(ut.operator) &&
				this.subs.equals(ut.subs);
	}

	@Override
	public int hashCode() {
		int ret = operator.hashCode();
		int base = 10;
		int i = 1;

		for (SMTTerm sub : subs) {
			ret = ret + sub.hashCode() * (base^i);
			i++;
		}

		return ret;
	}

	public String toString(int nestPos) {
		StringBuffer tab =  new StringBuffer();
		for(int i = 0; i< nestPos; i++) {
			tab = tab.append(" ");
		}

		StringBuffer buff = new StringBuffer();
		buff.append(tab);
		if (subs.size() > 0) {
			buff.append("(");
		}
		buff.append(operator.getOpName());
		for(SMTTerm f : subs){
		    buff.append("\n");
		    buff.append(f.toString(nestPos+1));
		}
		if (subs.size() > 0) {
			buff.append("\n");
			buff.append(tab);
			buff.append(")");
		}
		return buff.toString();
	}
}
