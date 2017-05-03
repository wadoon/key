package de.uka.ilkd.key.dependencycluster.po;

import de.uka.ilkd.key.proof.init.AbstractOperationPO;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.InfFlowProofSymbols;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.TempEventLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationBySpec;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.util.DependencyClusterSpec;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.Lowlist.Direction;

public class DependencyClusterContractPO extends AbstractOperationPO
        implements ContractPO {
    
    private final DependencyClusterContract contract;
    
    private final ProofObligationVars symbExecVars;

    private final IFProofObligationVars ifVars;
    
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();
    
    public DependencyClusterContractPO(InitConfig initConfig, DependencyClusterContract contract) {
        super(initConfig, contract.getName());
        
        this.contract = contract;
        
        //TODO JK Christoph creates variables here and adds "information flow symbols"? Not completely sure yet what is needed and what to do with them
        final IProgramMethod pm = contract.getTarget();
        symbExecVars =
                new ProofObligationVars(pm, contract.getKJT(), environmentServices);

        assert (symbExecVars.pre.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(symbExecVars, environmentServices);
        
        
        for (Term formalParam : symbExecVars.formalParams) {
            infFlowSymbols.add(formalParam);
        }
        for (Term formalParam : ifVars.c1.formalParams) {
            infFlowSymbols.add(formalParam);
        }
        for (Term formalParam : ifVars.c2.formalParams) {
            infFlowSymbols.add(formalParam);
        }
    
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;

        final Services proofServices = postInit();  
        
        final DependencyClusterPOFormulaFactory factory = new DependencyClusterPOFormulaFactory(contract, symbExecVars, ifVars, proofServices);
    
        assignPOTerms(factory.completeFormula());
        
        collectClassAxioms(contract.getKJT(), proofConfig);

        DependencyClusterTacletFactory tacletFactory = new DependencyClusterTacletFactory(contract, proofConfig, ifVars);
        RewriteTaclet equivEventTaclet = tacletFactory.getEventEquivalenceTaclet();               
        register(equivEventTaclet, proofConfig);
        //TODO JK is another justification better? Reference the contract for example?
        proofConfig.registerRule(equivEventTaclet, AxiomJustification.INSTANCE);
        
        RewriteTaclet invisibilityTaclet = tacletFactory.getInvisibilityTaclet();             
        register(invisibilityTaclet, proofConfig);
        //TODO JK is another justification better? Reference the contract for example?
        proofConfig.registerRule(invisibilityTaclet, AxiomJustification.INSTANCE);
        
    }

    @Override
    public boolean implies(ProofOblInput po) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public KeYJavaType getContainerType() {
        return contract.getKJT();
    }

    @Override
    public DependencyClusterContract getContract() {
        return (DependencyClusterContract) contract;
    }

    @Override
    public Term getMbyAtPre() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }

    @Override
    protected boolean isTransactionApplicable() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }

    @Override
    protected ImmutableList<StatementBlock> buildOperationBlocks(
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar, ProgramVariable resultVar,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term getPre(List<LocationVariable> modHeaps,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term getPost(List<LocationVariable> modHeaps,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, ProgramVariable exceptionVar,
            Map<LocationVariable, LocationVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term getGlobalDefs(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
            Map<Term, Term> heapToAtPre, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    protected Modality getTerminationMarker() {
        return getContract().getModality();
    }

    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }
    
    private void createAndRegisterEquivEventTaclet() {
        TempEventLDT ldt = proofConfig.getServices().getTypeConverter().getTempEventLDT();
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        //TODO JK remove preceding As
        tacletBuilder.setDisplayName("AAAEquivEventDef");
        tacletBuilder.setName(new Name("AAAEquivEventDef"));
        
        Sort calltypeSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("Calltype");
        Sort dirSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("CallDirection");
        Sort objectSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("java.lang.Object");
        Sort methodSort = (Sort) proofConfig.getServices().getNamespaces().sorts().lookup("Method");
        Sort seqSort = proofConfig.getServices().getTypeConverter().getSeqLDT().targetSort();
        Sort heapSort = proofConfig.getServices().getTypeConverter().getHeapLDT().targetSort();
        
        Term calltype1 = tb.var(SchemaVariableFactory.createTermSV(new Name("calltype1"), calltypeSort, false, false));
        Term calltype2 = tb.var(SchemaVariableFactory.createTermSV(new Name("calltype2"), calltypeSort, false, false));
        
        Term direction1 = tb.var(SchemaVariableFactory.createTermSV(new Name("direction1"), dirSort, false, false));
        Term direction2 = tb.var(SchemaVariableFactory.createTermSV(new Name("direction1"), dirSort, false, false));    
        
        Term component1 = tb.var(SchemaVariableFactory.createTermSV(new Name("component1"), objectSort, false, false));
        Term component2 = tb.var(SchemaVariableFactory.createTermSV(new Name("component2"), objectSort, false, false));
        
        Term service1 = tb.var(SchemaVariableFactory.createTermSV(new Name("service1"), methodSort, false, false));
        Term service2 = tb.var(SchemaVariableFactory.createTermSV(new Name("service2"), methodSort, false, false));
        
        Term params1 = tb.var(SchemaVariableFactory.createTermSV(new Name("params1"), seqSort, false, false));
        Term params2 = tb.var(SchemaVariableFactory.createTermSV(new Name("params2"), seqSort, false, false));
        
        Term heap1 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false));
        Term heap2 = tb.var(SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false));        
        
        Term event1 = tb.func(ldt.evConst(), calltype1, direction1, component1, service1, params1, heap1);
        Term event2 = tb.func(ldt.evConst(), calltype2, direction2, component2, service2, params2, heap2);
        
        Term find = tb.func(ldt.equivEvent(), event1, event2);
        tacletBuilder.setFind(find);
        
        //Build replace term
        Term event1Invis = tb.func(ldt.invEvent(), event1);
        Term event2Invis = tb.func(ldt.invEvent(), event2);
        Term bothInvis = tb.and(event1Invis, event2Invis);
        
        Term sameType = tb.equals(calltype1, calltype2);
        Term sameDirection = tb.equals(direction1, direction2);
        Term samePartner = tb.equals(component1, component2); //TODO JK does simple equality work here??? Probably change this!
        Term sameService = tb.equals(service1, service2);
        Term sameMetadata = tb.and(sameType, sameDirection, samePartner, sameService);
        
        
        Term updatedParams1 =tb.elementary(ldt.getCurrentParams(), params1);
        Term updatedParams2 =tb.elementary(ldt.getCurrentParams(), params2); //TODO JK probably we'll need to make an updated heap as well. In the long run use a function here anyway...
        
        ImmutableList<Term> collectedConditionsForEquivalenceOfVisibleEvents = ImmutableSLList.<Term>nil();
        for (Lowlist list: contract.getSpecs().head().getLowIn()) {
            Term checkDirection = tb.func(ldt.evIncoming());
            Term checkCalltype;
            if (list.getCallType() == Lowlist.MessageType.CALL) {
                checkCalltype = tb.func(ldt.evCall());
            } else {
                checkCalltype = tb.func(ldt.evTerm());
            }
            Term checkComponent = list.getCommunicationPartner().getTerm(); //TODO JK probably not that easy! Maybe we need to evaluate the component on a specific Heap or something
            Term checkService = tb.func(ldt.getMethodIdentifier(list.getService().getMethodDeclaration(), proofConfig.getServices()));
            
            Term dirEq = tb.equals(direction1, checkDirection);
            Term typeEq = tb.equals(calltype1, checkCalltype);
            Term compEq = tb.equals(component1, checkComponent); //TODO JK probably not that easy! Object equalities are annoying...
            Term servEq = tb.equals(service1, checkService);
            Term metadataFits = tb.and(dirEq, typeEq, compEq, servEq);

            ImmutableList<Term> expressionsEq = ImmutableSLList.<Term>nil();
            for (Term term: list.getLowTerms()) {
                System.out.println(checkDirection + "." + checkComponent + "." + checkService + "." + checkCalltype + ":" + term + " is of sort " + term.sort());
                
                Term expressionComparison = null;
                
                //TODO JK Parser returns some "boolean" expressions (for example with > operator) as Formulas, not as expressions, so we need special treatment for those (can't be in sequences, dont have a = relation...)
                if (term.sort().equals(tb.tt().sort())) {   
                    Term t1 = tb.apply(updatedParams1, term);
                    Term t2 = tb.apply(updatedParams1, term);
                    expressionComparison = tb.equals(t1, t2);
                }
                
                //TODO JK continue here, cases for objects and basic types
                
                if (!(expressionComparison == null)) {
                    expressionsEq = expressionsEq.append(expressionComparison);
                }

            }
            
            if (!expressionsEq.isEmpty()) {
                collectedConditionsForEquivalenceOfVisibleEvents = collectedConditionsForEquivalenceOfVisibleEvents.append(tb.and(metadataFits, tb.and(expressionsEq)));
            }
        }
        Term visibleEquivalence = tb.and(sameMetadata, tb.or(collectedConditionsForEquivalenceOfVisibleEvents));
        Term replaceWith = tb.or(bothInvis, visibleEquivalence);        
        tacletBuilder.addGoalTerm(replaceWith);
        
        
        
        
        
        
        
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)proofConfig.ruleSetNS().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
        System.out.println(taclet);
  
        register(taclet, proofConfig);
        //TODO JK is another justification better? Reference the contract for example?
        proofConfig.registerRule(taclet, AxiomJustification.INSTANCE);
               

    }
    
    //TODO JK falscher Ansatz, entfernen
    private void createAndRegisterEquivEventTaclet(Lowlist lowlist) {
        TempEventLDT ldt = proofConfig.getServices().getTypeConverter().getTempEventLDT();
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<RewriteTaclet>();
        
        //TODO JK remove preceding As
        String name = lowlist.getComponent().getTerm() + "." + lowlist.getService().getName() + "." + lowlist.getDirection().name();
        tacletBuilder.setDisplayName("AAAEquivEventDefFor_" + name);
        tacletBuilder.setName(new Name("AAAEquivEventDefFor_" + name));
        
        
        
        Term calltype;
        Term direction;
        
        if (lowlist.getDirection() == Direction.IN) {
            direction = tb.func(ldt.evIncoming());
            if (lowlist.getComponent().getTerm().equals(contract.getSelfVar())) {
                calltype = tb.func(ldt.evCall());
            } else {
                calltype = tb.func(ldt.evTerm());
            }
        } else {
            direction = tb.func(ldt.evOutgoing());
            if (lowlist.getComponent().getTerm().equals(contract.getSelfVar())) {
                calltype = tb.func(ldt.evTerm());
            } else {
                calltype = tb.func(ldt.evCall());
            }            
        }
        
        Term service = tb.func(ldt.getMethodIdentifier(lowlist.getService().getMethodDeclaration(), proofConfig.getServices()));
        
        //TODO JK ist this the right sort?
        Sort seqSort = proofConfig.getServices().getTypeConverter().getSeqLDT().targetSort();
        Sort heapSort = proofConfig.getServices().getTypeConverter().getHeapLDT().targetSort();
        //TODO JK what about rigidness and strictness values??? Is TermSV right? Or do we need another kind of SV?
        SchemaVariable params1 = SchemaVariableFactory.createTermSV(new Name("params1"), seqSort, false, false);
        SchemaVariable params2 = SchemaVariableFactory.createTermSV(new Name("params2"), seqSort, false, false);
        
        SchemaVariable heap1 = SchemaVariableFactory.createTermSV(new Name("heap1"), heapSort, false, false);
        SchemaVariable heap2 = SchemaVariableFactory.createTermSV(new Name("heap2"), heapSort, false, false);
        
        
        Term event1 = tb.func(ldt.evConst(), calltype, direction, lowlist.getComponent().getTerm(), service, tb.var(params1), tb.var(heap1));
        Term event2 = tb.func(ldt.evConst(), calltype, direction, lowlist.getComponent().getTerm(), service, tb.var(params2), tb.var(heap2));
        
        
        Sort eventSort = (Sort)proofConfig.getServices().getNamespaces().sorts().lookup("Event");
        
               
        
        //TODO JK varconds needed? like notFreeIn...
        
        Term find = tb.func(ldt.equivEvent(), event1, event2);
        
        //TODO JK Calltype, CallDirection, commpartner, Method, params, Heap... viele vergleiche und details wichtig, wie heap einarbeiten, wie object sensitivity...
        //TODO JK add equivalence if both invisible
        ImmutableList<Term> lowIn = lowlist.getLowTerms();

        
        /*
        Term lowInSeq = tb.seq(lowIn);
        Term updatedLowInSeq1 = tb.elementary(tb.var(ldt.getCurrentParams()), tb.func(ldt.evGetArgs(), tb.var(e1)));
        Term updatedLowInSeq2 = tb.elementary(tb.var(ldt.getCurrentParams()), tb.func(ldt.evGetArgs(), tb.var(e2)));
        Term seqEquality = tb.equals(updatedLowInSeq1, updatedLowInSeq2); //TODO JK right now completely ignoring heaps, object sensitivity...
        */
        
        Term replaceWith = tb.func(ldt.equivEvent(), event2, event1);

        tacletBuilder.setFind(find);
        tacletBuilder.addGoalTerm(replaceWith);
        
        
        
        
        
        
        
        
        //TODO JK which ruleset is correct?
        tacletBuilder.addRuleSet((RuleSet)proofConfig.ruleSetNS().lookup(new Name("simplify_enlarging")));  
        
        RewriteTaclet taclet = tacletBuilder.getRewriteTaclet();
  
        register(taclet, proofConfig);
        //TODO JK is another justification better? Reference the contract for example?
        proofConfig.registerRule(taclet, AxiomJustification.INSTANCE);

    }

}
