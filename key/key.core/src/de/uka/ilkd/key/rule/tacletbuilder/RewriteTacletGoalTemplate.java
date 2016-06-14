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

package de.uka.ilkd.key.rule.tacletbuilder;

import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.rule.Taclet;

/** this class inherits from TacletGoalTemplate. It is used if there is a
 * replacewith in the ruleGoals that replaces a term by another
 * term. For a sequent {@link AntecSuccTacletGoalTemplate}
 */
public class RewriteTacletGoalTemplate extends TacletGoalTemplate {

    /** term that replaces another one */
    private JavaDLTerm replacewith;

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules IList<Taclet> contains the new allowed rules
     * at this branch 
     *@param replacewith the JavaDLTerm that replaces another one
     *@param pvs the set of schema variables
     */
    public RewriteTacletGoalTemplate(Sequent             addedSeq,
				     ImmutableList<Taclet>        addedRules,				     
				     JavaDLTerm                replacewith,
				     ImmutableSet<SchemaVariable> pvs) {
	super(addedSeq, addedRules, pvs);
	TacletBuilder.checkContainsFreeVarSV(replacewith, null, "replacewith term");
	this.replacewith = replacewith;
    }

    public RewriteTacletGoalTemplate(Sequent addedSeq,
			   ImmutableList<Taclet> addedRules,
			   JavaDLTerm replacewith) {
	this(addedSeq, addedRules, replacewith,
	     DefaultImmutableSet.<SchemaVariable>nil());
    }


    public RewriteTacletGoalTemplate(JavaDLTerm replacewith) {
	this(Sequent.EMPTY_SEQUENT, ImmutableSLList.<Taclet>nil(),
             replacewith);
    }


    /** a Taclet may replace a JavaDLTerm by another. The new JavaDLTerm is returned.     
     * @return JavaDLTerm being paramter in the rule goal replacewith(Seq)
     */
    public JavaDLTerm replaceWith() {
	return replacewith;
    }
    
    /**
     * rertieves and returns all variables that are bound in the 
     * goal template
     * @return all variables that occur bound in this goal template
     */
    @Override
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(replaceWith());
        return bvv.getBoundVariables().union(super.getBoundVariables());
    }
    
    /**
     * @return JavaDLTerm being paramter in the rule goal replacewith(term)
     */
    @Override
    public Object replaceWithExpressionAsObject() {
	return replacewith;
    }


    @Override
    public boolean equals(Object o) {
       if (!super.equals(o)) {
          return false;
       }
       final RewriteTacletGoalTemplate other = (RewriteTacletGoalTemplate) o;
       return replacewith.equals(other.replacewith);
    }
    
    @Override
    public int hashCode(){
    	int result = 17;
    	result = 37 * result * super.hashCode();
    	result = 37 * result * replacewith.hashCode();
    	return result;
    }

    
    /** toString */
    @Override
    public String toString() {
	String result=super.toString();
	result+="\\replacewith("+replaceWith()+") ";       
	return result;
    }

}