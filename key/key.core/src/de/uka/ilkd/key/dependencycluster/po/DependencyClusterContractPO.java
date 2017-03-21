package de.uka.ilkd.key.dependencycluster.po;

import de.uka.ilkd.key.proof.init.AbstractOperationPO;

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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.DependencyClusterContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import de.uka.ilkd.key.util.DependencyClusterSpec;
import de.uka.ilkd.key.util.InfFlowSpec;

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

        /*
        System.out.println(symbExecVars.formalParams);
        System.out.println(symbExecVars.exceptionParameter);
        System.out.println(symbExecVars.pre);
        System.out.println(symbExecVars.post);
        */
        
        assert (symbExecVars.pre.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(symbExecVars, environmentServices);
        
        /*
        System.out.println(ifVars.c1.formalParams);
        System.out.println(ifVars.c1.exceptionParameter);
        System.out.println(ifVars.c1.pre);
        System.out.println(ifVars.c1.post);
        
        System.out.println(ifVars.c2.formalParams);
        System.out.println(ifVars.c2.exceptionParameter);
        System.out.println(ifVars.c2.pre);
        System.out.println(ifVars.c2.post);
        */
        
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
        
        //Term test = tb.apply(ifVars.c1.pre.heap, tb.getBaseHeap());
        //assignPOTerms(tb.imp(tb.geq(tb.zTerm(1), tb.zTerm(4)), tb.ff()));
        
        //TODO JK build the correct obligation properly, this is a placeholder dummy test ;)
        ImmutableList<InfFlowSpec> infFlowSpecs = ImmutableSLList.<InfFlowSpec>nil();
        
        for (DependencyClusterSpec spec: contract.getSpecs()) {
            InfFlowSpec infFlowSpec = new InfFlowSpec(spec.getLowState(), spec.getLowState(), ImmutableSLList.<Term>nil());
            infFlowSpecs = infFlowSpecs.append(infFlowSpec);
        }
        
        InformationFlowContract infFlowContract = 
                new InformationFlowContractImpl(contract.getName(), 
                        contract.getKJT(), 
                        contract.getTarget(), 
                        contract.getSpecifiedIn(), 
                        contract.getModality(), 
                        contract.getPre(), 
                        contract.getMby(), 
                        contract.getMod(), 
                        contract.hasModifiesClause(), 
                        contract.getSelfVar(), 
                        contract.getParams(), 
                        contract.getResult(), 
                        contract.getExc(), 
                        contract.getHeapAtPre(), 
                        contract.getDep(),
                        infFlowSpecs,
                        true);
        // create proof obligation
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(infFlowContract, ifVars.c1,
                                                   ifVars.c2, proofServices);
        
        BasicPOSnippetFactory f1 =
                POSnippetFactory.getBasicFactory(contract, ifVars.c1, proofServices);
        
        
        //TODO JK wahrscheinlich noch nicht ganz korrekt, z.B. noch "richtige" hist auswählen...
        final TempEventLDT ldt = proofServices.getTypeConverter().getTempEventLDT();
        final Term event = tb.func(ldt.evConst(), 
                tb.func(ldt.evCall()), 
                tb.func(ldt.evIncoming()), 
                symbExecVars.pre.self, //TODO JK richtige self variable?
                tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), proofServices)),
                tb.seq(symbExecVars.formalParams), 
                symbExecVars.pre.heap);
        final Term actualHistory = tb.var(ldt.getHist());
        final Term historyWithCallEvent = tb.seqSingleton(event);
        final Term initHistory = tb.equals(actualHistory, historyWithCallEvent);
     
        
        
        
  
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);

        final Term post =
                f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        
        final Term finalTerm = tb.imp(selfComposedExec, post);
        //final Term finalTerm = tb.imp(selfComposedExec, post);
        
        
        
        //addLabeledIFSymbol(selfComposedExec);
        assignPOTerms(finalTerm);
        
        collectClassAxioms(contract.getKJT(), proofConfig);
        
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

}
