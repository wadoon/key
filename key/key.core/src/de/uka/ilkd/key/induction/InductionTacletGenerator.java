package de.uka.ilkd.key.induction;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;

public class InductionTacletGenerator {
	
	private static final String COUNTER_NAME = "inductionRewrite";
	
	public static void generate(Term t, Services s, RelationDescription selected){
		TacletGenerator generator = TacletGenerator.getInstance();
		Name tacletName = new Name("inductionRewrite_" + s.getCounter(COUNTER_NAME).getCountPlusPlus());
		RuleSet ruleset = (RuleSet)s.getNamespaces().ruleSets().elements().head();//TODO: check if this works
		ImmutableList<ProgramVariable> programVars = ImmutableSLList.nil();
		Taclet tac = generator.generateRewriteTaclet(
				tacletName,
				t,
				InductionFormulaCreator.buildFormula(t, s, selected), 
				programVars, 
				ruleset, 
				s
				);
		
		/*
		generator.generateAxiomTaclet(tacletName, originalAxiom, programVars, kjt, ruleSet, services)
		generator.generateContractAxiomTaclets(name, originalPre, originalPost, originalMby, kjt, target, heaps, originalSelfVar, originalResultVar, atPreVars, originalParamVars, toLimit, satisfiabilityGuard, services)
		generator.generateFunctionalRepresentsTaclets(name, originalPreTerm, originalRepresentsTerm, kjt, target, heaps, self, paramVars, atPreVars, toLimit, satisfiability, services)
		generator.generatePartialInvTaclet(name, heapSVs, selfSV, eqSV, term, kjt, toLimit, isStatic, eqVersion, services)
		generator.generateRelationalRepresentsTaclet(tacletName, originalAxiom, kjt, target, heaps, self, paramVars, atPreVars, satisfiabilityGuard, services)
		*/
		s.getSpecificationRepository(); //RuleJustification?
		
		SVInstantiations insts = SVInstantiations.EMPTY_SVINSTANTIATIONS;
		
		s.getProof().openGoals().head().addTaclet(tac, insts, true);
	}

}
