package de.uka.ilkd.key.informationflow.po.snippet;
//TODO JK move this to de.uka.ilkd.key.dependencycluster.po as soon as I find a way to reuse simons code without code duplication and ugly hacks like this

import java.util.Iterator;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.BasicSnippetData;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.ldt.TempEventLDT;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.DependencyClusterContract;

public class SymbExecWithHistFactory {
    private final DependencyClusterContract contract;
    private final ProofObligationVars ifVars;
    private final Services services;
    private final TermBuilder tb;
    private final TempEventLDT ldt;
    private final ProofObligationVars symbExecVars;
    private final BasicPOSnippetFactory f;
    private final Term postHistory;
    
    public SymbExecWithHistFactory(DependencyClusterContract contract, ProofObligationVars symbExecVars, ProofObligationVars ifVars, Services services, Term postHistory) {
        this.contract = contract;
        this.ifVars = ifVars;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.ldt = services.getTypeConverter().getTempEventLDT();
        this.symbExecVars = symbExecVars;
        //TODO JK check sort of postHistory
        this.postHistory = postHistory;
        
        f = POSnippetFactory.getBasicFactory(contract, ifVars, services);
    }
    
    public Term callEvent() {
        return tb.func(ldt.evConst(), 
                tb.func(ldt.evCall()), 
                tb.func(ldt.evIncoming()), 
                symbExecVars.pre.self,  //TODO JK use another partner instead of self
                tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), services)),
                tb.seq(ifVars.formalParams), 
                ifVars.pre.heap);
    }
    
    public Term historyWithCallEvent() {
        return tb.seqSingleton(callEvent());
    }
    
    public Term updateHistoryWithCallEvent() {
        return tb.elementary(realHistory(), historyWithCallEvent());
    }
    
    public Term initialHistoryEquality() {
        return tb.equals(realHistory(), historyWithCallEvent());
    }
    
    public Term terminationEvent() {
       return tb.func(ldt.evConst(), 
                tb.func(ldt.evTerm()), 
                tb.func(ldt.evOutgoing()), 
                symbExecVars.pre.self,  //TODO JK use another partner instead of self
                tb.func(ldt.getMethodIdentifier(contract.getTarget().getMethodDeclaration(), services)),
                tb.seq(ifVars.post.result), 
                ifVars.post.heap);    
    }
        
    public Term historyWithTermEvent() {
        return tb.seqConcat(realHistory(), tb.seqSingleton(terminationEvent()));
    }
    
    //TODO JK this isn't really needed, is it?
    public Term updateHistoryWithTermEvent() {
        return tb.elementary(realHistory(), historyWithTermEvent());
    }
    
    public Term postHistoryEquality() {
        return tb.equals(postHistory, historyWithTermEvent());
    }
    
    public Term pre() {
        final Term freePre =
                f.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre =
                f.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        return tb.and(freePre, initialHistoryEquality(), contractPre);
    }
    
    //TODO JK copied from christoph - how to reuse his code properly???
    public Term symbolicExecutionWithPost() {
        assert ifVars.exceptionParameter.op() instanceof LocationVariable :
                "Something is wrong with the catch variable";
    
        ImmutableList<Term> posts = ImmutableSLList.<Term>nil();
        if (ifVars.post.self != null) {
            posts = posts.append(tb.equals(ifVars.post.self, ifVars.pre.self));
        }
        
        //TODO JK I don't think we need a result var
        /*
        if (ifVars.post.result != null) {
            posts = posts.append(tb.equals(ifVars.post.result,
                    ifVars.pre.result));
        }
        */
        posts = posts.append(tb.equals(ifVars.post.exception,
                ifVars.pre.exception));
        posts = posts.append(tb.equals(ifVars.post.heap, tb.getBaseHeap()));
        
        
        posts = posts.append(postHistoryEquality());
        
        BasicSnippetData d = new BasicSnippetData(contract, services);
        final Term prog = buildProgramTerm(d, ifVars, tb.and(posts), tb);
        return prog;
    }
    
    public Term updatedExecutionWithPreAndPost() {
        final Term execWithPre = tb.and(pre(), symbolicExecutionWithPost());

        final Term updateHeap = tb.elementary(tb.getBaseHeap(), ifVars.pre.heap);
        
        //TODO JK no need to update the history I think
        return tb.apply(updateHeap, tb.apply(updateHistoryWithCallEvent(), execWithPre));
    }
    
    public Term filteredPostHistory() {
        return tb.func(ldt.filterVisible(), postHistory);
    }
    
    
    private Term realHistory() {
        return tb.var(ldt.getHist());
    }
    
    //TODO JK the following code is mostly copied from Christophs BasicSymbolicExecutionSnippet, but I don't really know how to properly reuse that code without rewriting christophs factory
    private Term buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  Term postTerm,
                                  TermBuilder tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "program-term for a contract without modality.");
        }
        assert Modality.class.equals(BasicSnippetData.Key.MODALITY.getType());
        Modality modality = (Modality) d.get(
                BasicSnippetData.Key.MODALITY);


        //create java block
        final JavaBlock jb = buildJavaBlock(d, vs.formalParams,
                                            vs.pre.self != null
                                            ? vs.pre.self.op(ProgramVariable.class)
                                            : null,
                                            vs.pre.result != null
                                            ? vs.pre.result.op(ProgramVariable.class)
                                            : null,
                                            vs.pre.exception != null
                                            ? vs.pre.exception.op(ProgramVariable.class)
                                            : null,
                                            vs.exceptionParameter.op(LocationVariable.class));

        //create program term
        final Modality symbExecMod;
        if (modality == Modality.BOX) {
            symbExecMod = Modality.DIA;
        } else {
            symbExecMod = Modality.BOX;
        }
        final Term programTerm = tb.prog(symbExecMod, jb, postTerm);
        //final Term programTerm = tb.not(tb.prog(modality, jb, tb.not(postTerm)));

        //create update
        Term update = tb.skip();
        Iterator<Term> formalParamIt = vs.formalParams.iterator();
        Iterator<Term> paramIt = vs.pre.localVars.iterator();
        while (formalParamIt.hasNext()) {
            Term formalParam = formalParamIt.next();
            LocationVariable formalParamVar =
                    formalParam.op(LocationVariable.class);
            Term paramUpdate = tb.elementary(formalParamVar,
                                             paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }

        return tb.apply(update, programTerm);
    }

    private JavaBlock buildJavaBlock(BasicSnippetData d,
                                     ImmutableList<Term> formalPars,
                                     ProgramVariable selfVar,
                                     ProgramVariable resultVar,
                                     ProgramVariable exceptionVar,
                                     LocationVariable eVar) {
        IObserverFunction targetMethod =
                (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        if (!(targetMethod instanceof IProgramMethod)) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "java-block for an observer which is no program method.");
        }
        JavaInfo javaInfo = d.services.getJavaInfo();
        IProgramMethod pm = (IProgramMethod) targetMethod;

        //create method call
        ProgramVariable[] formalParVars = extractProgramVariables(formalPars);
        final ImmutableArray<Expression> formalArray =
                new ImmutableArray<Expression>(formalParVars);
        final StatementBlock sb;
        if (pm.isConstructor()) {
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 =
                formalArray.toArray(new Expression[formalArray.size()]);
            KeYJavaType forClass =
                    (KeYJavaType) d.get(BasicSnippetData.Key.FOR_CLASS);
            final New n =
                    new New(formalArray2, new TypeRef(forClass),
                            null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            sb = new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                new MethodBodyStatement(pm, selfVar, resultVar, formalArray);
            sb = new StatementBlock(call);
        }

        //type of the variable for the try statement
        final KeYJavaType eType =
            javaInfo.getTypeByClassName("java.lang.Throwable");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);

        //create try statement
        final CopyAssignment nullStat =
            new CopyAssignment(exceptionVar, NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl =
            new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec,
                    false);
        final CopyAssignment assignStat =
            new CopyAssignment(exceptionVar, eVar);
        final Catch catchStat =
            new Catch(excDecl, new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[]{catchStat});
        final StatementBlock sb2 = new StatementBlock(
                new Statement[]{nullStat, tryStat});

        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);

        return result;
    }


    private ProgramVariable[] extractProgramVariables(
                                                      ImmutableList<Term> formalPars)
            throws IllegalArgumentException {
        ProgramVariable[] formalParVars = new ProgramVariable[formalPars.size()];
        int i = 0;
        for(Term formalPar : formalPars) {
            formalParVars[i++] = formalPar.op(ProgramVariable.class);
        }
        return formalParVars;
    }

    public Term wellformedHistory() {
        return tb.and(tb.func(ldt.wellformedList(), postHistory),tb.func(ldt.wellformedListCoop(), postHistory));
    }

}
