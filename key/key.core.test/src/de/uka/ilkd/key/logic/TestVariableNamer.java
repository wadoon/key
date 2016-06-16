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

package de.uka.ilkd.key.logic;

import java.util.Iterator;

import junit.framework.TestCase;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.PosInTerm;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.TacletIndexKit;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecTacletBuilder;


public class TestVariableNamer extends TestCase {
    

    private final Proof proof = new Proof("TestVariableNamer", 
    		new InitConfig(new Services(AbstractProfile.getDefaultProfile())));
    private final Services services = proof.getServices();
    private final ProgramVariable x     = constructProgramVariable("x");
    private final ProgramVariable xx    = constructProgramVariable("x");
    private final ProgramVariable y     = constructProgramVariable("y");
    private final ProgramVariable x_1   = constructProgramVariable("x_1");
    private final ProgramVariable x_2   = constructProgramVariable("x_2");
    private final ProgramVariable var_1 = constructProgramVariable("var_1");
    private final ProgramVariable var_2 = constructProgramVariable("var_2");
    private final SequentFormula<JavaDLTerm> formulaWithX    = constructFormula(x);
    private final SequentFormula<JavaDLTerm> formulaWithX_1  = constructFormula(x_1);
    private final SequentFormula<JavaDLTerm> formulaWithVar_1= constructFormula(var_1);
    private final SchemaVariable variableSV =
    	  SchemaVariableFactory.createProgramSV(new ProgramElementName("sv"),
						ProgramSVSort.VARIABLE,
						false);
    
    
    public TestVariableNamer(String name) {
	super(name);
    }
        

    private ProgramVariable constructProgramVariable(ProgramElementName name) {
	KeYJavaType myKeyJavaType
	    = new KeYJavaType(new SortImpl(new Name("mysort")));
    	return new LocationVariable(name, myKeyJavaType);
    }

    private ProgramVariable constructProgramVariable(String name) {
    	ProgramElementName pen = VariableNamer.parseName(name);
	assertTrue(pen.toString().equals(name));
    	return constructProgramVariable(pen);
    }

    private SequentFormula<JavaDLTerm> constructFormula(ProgramVariable containedVar) {
    	Statement statement = new PostIncrement(containedVar);
    	StatementBlock statementBlock = new StatementBlock(statement);
    	JavaBlock javaBlock = JavaBlock.createJavaBlock(statementBlock);

	JavaDLTerm term = services.getTermBuilder().dia(javaBlock, services.getTermBuilder().tt());

	return new SequentFormula<>(term);
    }

    
    private PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> constructPIO(SequentFormula<JavaDLTerm> formula) {
    	return new PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>(formula, PosInTerm.<JavaDLTerm>getTopLevel(), true);
    }


    private Goal constructGoal(SequentFormula<JavaDLTerm> containedFormula) {
    	Semisequent empty = Semisequent.nil();
    	Semisequent ante = empty.insert(0, containedFormula).semisequent();
	Semisequent succ = empty;

    	Sequent seq = Sequent.createSequent(ante, succ);
	Node node = new Node(proof, seq);

	TacletIndex tacletIndex = TacletIndexKit.getKit().createTacletIndex();
	BuiltInRuleAppIndex builtInRuleAppIndex = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
	RuleAppIndex ruleAppIndex = new RuleAppIndex(tacletIndex,
						     builtInRuleAppIndex, proof.getServices());

	return new Goal(node, ruleAppIndex);
    }


    private void addGlobal(Goal goal, ProgramVariable globalVar) {
 	ImmutableSet<ProgramVariable> globals = goal.getGlobalProgVars().add(globalVar);
	goal.setGlobalProgVars(globals);
    }


    private boolean inGlobals(Goal goal, ProgramVariable globalVar) {
        for (ProgramVariable programVariable : goal.getGlobalProgVars()) {
            if (programVariable == globalVar) {
                return true;
            }
        }
	return false;
    }
    
    private void addTacletApp(Goal goal, ProgramVariable containedVar) {
	JavaDLTerm findTerm = services.getTermBuilder().tt();
   	AntecTacletBuilder builder = new AntecTacletBuilder();
	builder.setFind(findTerm);
    	AntecTaclet taclet = builder.getAntecTaclet();
    	NoPosTacletApp app = NoPosTacletApp.createNoPosTacletApp(taclet);

	SchemaVariable sv
		= SchemaVariableFactory.createProgramSV(new ProgramElementName("sv"),
						        ProgramSVSort.STATEMENT,
						        false);
    	Statement statement = new PostIncrement(containedVar);
	app = (NoPosTacletApp) app.addCheckedInstantiation(sv, statement, 
                goal.proof().getServices(), false);

    	goal.ruleAppIndex().tacletIndex().add(app);
    }
    
    
    private boolean inTacletApps(Goal goal, ProgramVariable containedVar) {
	RuleAppIndex ruleAppIndex = goal.ruleAppIndex();
	TacletIndex tacletIndex = ruleAppIndex.tacletIndex();
	ImmutableList<NoPosTacletApp> noPosTacletApps
		= tacletIndex.getPartialInstantiatedApps();

        for (NoPosTacletApp noPosTacletApp : noPosTacletApps) {
            SVInstantiations insts = noPosTacletApp.instantiations();
            Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it2;
            it2 = insts.pairIterator();
            while (it2.hasNext()) {
                ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> e = it2.next();
                Object inst = e.value().getInstantiation();
                if (inst instanceof PostIncrement
                        && ((PostIncrement) inst).getFirstElement() == containedVar) {
                    return true;
                }
            }
        }
	
	return false;
    }


    private void testTemporaryNames(VariableNamer vn) {
    	ProgramElementName name = vn.getTemporaryNameProposal("x");
	assertFalse(name.getProgramName().equals("x"));

	ProgramVariable v = constructProgramVariable(name);
	SequentFormula<JavaDLTerm> formula = constructFormula(v);
	Goal goal = constructGoal(formula);
	PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio = constructPIO(formula);
	v = vn.rename(v, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("x"));
    }


    public void testInnerRename() {    	
    	VariableNamer vn = services.getProgramServices().getInnerVarNamer();
	ProgramVariable v, w;

	PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio = constructPIO(formulaWithX);
 	Goal goal = constructGoal(formulaWithX);

	v = vn.rename(y, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("y"));

   	v = vn.rename(xx, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("x"));

        proof.getNamespaces().programVariables().addSafely(v);
	addGlobal(goal, v);
	w = vn.rename(x, goal, pio);
	assertFalse(w.getProgramElementName().getProgramName().equals("x"));
	assertTrue(inGlobals(goal, v));

	// Reset progVar namespace which was altered due to addGlobal()
	proof.getNamespaces().programVariables().reset();
	testTemporaryNames(vn);
    }


   
    
//    public void testInnerRenameInTacletApps() {
//     	VariableNamer vn = services.getVariableNamer();
//	ProgramVariable v;
//	
//	PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio = constructPIO(formulaWithX);
//	Goal goal = constructGoal(formulaWithX);
//        proof.getNamespaces().programVariables().addSafely(xx);
//	addGlobal(goal, xx);
//	addTacletApp(goal, x);
//	
//	v = vn.rename(x, goal, pio);
//	assertFalse(inTacletApps(goal, x));
//	assertTrue(inTacletApps(goal, v));
//    }
    
    public void testNameProposals() {
    	VariableNamer vn = services.getProgramServices().getInnerVarNamer();
	ProgramElementName proposal;

	PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio = constructPIO(formulaWithVar_1);
	Goal goal = constructGoal(formulaWithVar_1);
	
	proposal = vn.getNameProposalForSchemaVariable(null,
						       variableSV,
						       pio,
						       null,
						       null);
	assertTrue(proposal.toString().equals("var_2"));

        proof.getNamespaces().programVariables().addSafely(var_2);
	addGlobal(goal, var_2);

	proposal = vn.getNameProposalForSchemaVariable("var",
						       variableSV,
						       pio,
						       null,
						       null);
	assertTrue(proposal.toString().equals("var_2"));
    }
    
    
    public void testInnerRenameUniqueness() {     	
    	VariableNamer vn = services.getProgramServices().getInnerVarNamer();
	ProgramVariable v;
	
	PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio = constructPIO(formulaWithX_1);
	Goal goal = constructGoal(formulaWithX_1);
        proof.getNamespaces().programVariables().addSafely(xx);
	addGlobal(goal, xx);
	addTacletApp(goal, x_2);
	
	v = vn.rename(x, goal, pio);
	assertTrue(v.getProgramElementName().getProgramName().equals("x_2"));
    }
}