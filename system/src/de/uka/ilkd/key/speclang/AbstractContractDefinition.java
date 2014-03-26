package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;

public class AbstractContractDefinition implements SpecificationElement{
	private final Term definedSymbol;
	private final Term definition;
	private KeYJavaType kjt;
	private final String name;
	public AbstractContractDefinition(Term definedSymbol, Term definition) {
		super();
		this.definedSymbol = definedSymbol;
		this.definition = definition;
		this.kjt = null;
		this.name = "expand_def_" + definedSymbol.op().name();
	}
	
	@SuppressWarnings("unchecked")
	public Taclet toTaclet(TermServices services){
		TacletGenerator TG = TacletGenerator.getInstance();
		
		//get variables of definedSymbol (reversed)
		
		ImmutableList<ProgramVariable> listVars = ImmutableSLList.<ProgramVariable>nil();
		for (Term pTerm: definedSymbol.subs()) {
			listVars = listVars.prepend((ProgramVariable)pTerm.op());
		}
		
		return TG.generateRewriteTaclet(new Name(name),
				definedSymbol,
				definition,
				listVars.reverse(),
                new RuleSet(new Name("expand_def")), 
                services); //services not needed
	}
	
	@Override
	public String getName() {
		return this.name;
	}
	@Override
	public String getDisplayName() {
		return this.name;
	}
	@Override
	public VisibilityModifier getVisibility() {
		assert false;
		return null;
	}
	@Override
	public KeYJavaType getKJT() {
		return kjt;
	}
	public void setKJT(KeYJavaType kjt) {
		this.kjt = kjt;
	}
	

	
}

