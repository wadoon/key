package de.uka.ilkd.key.proof.init.proofobligations;

import abs.frontend.ast.MethodImpl;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.keyabs.abs.*;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;

/**
 * generates a proof-obligation for proving that the class invariant is preserved by a given method
 */
public class ABSPreservesInvariantPO extends ABSAbstractPO {
    public static final String PRESERVES_INV_PO = "Preserves Invariant";

    private final ABSTermBuilder tb;
    private ImmutableSet<ABSClassInvariant> classInvariants;

    private final Name className;
    private final MethodImpl method;

    public ABSPreservesInvariantPO(ABSInitConfig initConfig,
                                   Name className,
                                   MethodImpl method) {
        super(initConfig);
        this.tb = services.getTermBuilder();
        this.className = className;
        this.method = method;
        this.classInvariants = repository.getClassInvariants(className.toString());
    }

    @Override
    public void readProblem() throws ProofInputException {

        ImmutableSet<Taclet> iinvs =
                collectInterfaceInvariantTaclets(initConfig.getServices());
        ImmutableSet<Taclet> cinvs =
                getClassInvariantTaclet(className, classInvariants, initConfig.getServices());

        initConfig.setTaclets(initConfig.getTaclets().union(cinvs).union(iinvs));

        final Sort anyInterfaceSort = services.getProgramInfo().getAnyInterfaceSort();

        LocationVariable history = services.getTypeConverter().getHistoryLDT().getHistory();
        LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
        Term wellFormedHistory = tb.wellFormedHistory(history, services);
        Term wellFormedHeap = tb.wellFormed(heap, services);

        Function _this = services.getTypeConverter().getThisConstant();
        
        problemTerm = tb.and(wellFormedHeap, wellFormedHistory, tb.not(tb.equals(tb.func(_this),
                tb.NULL(services))));



        Pair<ABSStatementBlock, ImmutableList<IProgramVariable>> methodAndParams =
                services.getProgramInfo().getMethodBody(method);

        services.getNamespaces().programVariables().addSafely(methodAndParams.second);
                

        Function methodLabel = services.getProgramInfo().getMethodLabelFor(method);

        LocationVariable result = new LocationVariable(new ProgramElementName(tb.newName(services, "result")),
                services.getProgramInfo().getKeYJavaType(method.getType().getQualifiedName()));
        LocationVariable future = new LocationVariable(new ProgramElementName(tb.newName(services, "future")),
                services.getProgramInfo().getKeYJavaType("ABS.StdLib.Fut"));
        
        ABSMethodFrame frame =
                new ABSMethodFrame(new ABSExecutionContext(
                        new ABSMethodLabel(methodLabel),
                        new ABSLocalVariableReference(result), new ABSLocalVariableReference(future)),
                        methodAndParams.first.getBody());

        ABSStatementBlock block = new ABSStatementBlock(frame);
        
        Term pre = tb.func((Function)services.getNamespaces().functions().lookup(new Name("Pre")), 
        		tb.var(history), tb.var(heap), tb.func(_this));

        problemTerm = tb.and(problemTerm, pre);
        problemTerm = tb.and(problemTerm, tb.classInvariant(history, heap, _this, services));

        Term post = tb.box(JavaBlock.createJavaBlock(block),
                tb.classInvariant(history, heap, _this, services));

        final LogicVariable caller = new LogicVariable(new Name(tb.newName(services, "caller")), anyInterfaceSort);
        final Term invocREv = createInvocationReactionEvent(_this, future, caller, methodAndParams.second, methodLabel);


        problemTerm = tb.applyElementary(services,
                tb.var(history),
                tb.seqConcat(services, tb.var(history),
                        tb.seqSingleton(services, invocREv)),
                tb.imp(problemTerm, post));

        problemTerm = assignMethodParameters(methodAndParams.second, problemTerm);

        // for all callers
        problemTerm = tb.all(caller, tb.imp(tb.not(tb.equals(tb.var(caller),
                tb.NULL(services))), problemTerm));

    }

    private Term createInvocationReactionEvent(Function _this,
                                               LocationVariable future,
                                               LogicVariable caller,
                                               ImmutableList<IProgramVariable> parameters,
                                               Function methodLabel) {
        Term argSeq = tb.seqEmpty(services);

        for (final IProgramVariable p : parameters) {
            argSeq = tb.seqConcat(services, argSeq, tb.seqSingleton(services, tb.var(p)));
        }

        final Function invocationReactionEvent =
                services.getTypeConverter().getHistoryLDT().getInvocationReactionEvent();
        return tb.func(invocationReactionEvent, tb.var(caller), tb.func(_this), tb.var(future),
                tb.func(methodLabel), argSeq);
    }

    private Term assignMethodParameters(ImmutableList<IProgramVariable> methodParameters,
                                        Term formula) {
    	Term result = formula;
    	for (IProgramVariable p : methodParameters) {
            LogicVariable plv = new LogicVariable(new Name(tb.newName(services, p.name().toString())), p.sort());
            result = tb.all(plv, tb.applyElementary(services, tb.var(p), tb.var(plv), result));
        }
        return result;
    }

    @Override
    public ProofAggregate getPO() throws ProofInputException {
        ProofSettings settings = initConfig.getSettings() != null
                ? initConfig.getSettings()
                : new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        final JavaModel absModel = initConfig.getProofEnv().getJavaModel();
        createProofHeader(absModel.getModelDir(), 
        		absModel.getClassPath(), 
        		absModel.getBootClassPath());
        
        return ProofAggregate.createProofAggregate(
                new Proof(name(), problemTerm, header, initConfig
                        .createTacletIndex(), initConfig
                        .createBuiltInRuleIndex(), initConfig.getServices(),
                        settings), name());
    }

    @Override
    public boolean implies(ProofOblInput po) {
        return po == this;
    }

    @Override
    public String name() {
        return ABSPreservesInvariantPO.PRESERVES_INV_PO + "_" +
                className + "_" + method.getMethodSig().getName();
    }
}
