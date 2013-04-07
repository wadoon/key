package de.uka.ilkd.key.proof.init.proofobligations;

import abs.frontend.ast.MethodImpl;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
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
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSTacletGenerator;
import de.uka.ilkd.keyabs.proof.mgt.ABSSpecificationRepository;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;

/**
 * generates a proof-obligation for proving that the class invariant is preserved by a given method
 */
public class ABSPreservesInvariantPO extends ABSAbstractPO {
    public static final String PRESERVES_INV_PO = "Preserves Invariant";
    private ImmutableSet<ABSClassInvariant> classInvariants;

    private final Name className;
    private final MethodImpl method;

    public ABSPreservesInvariantPO(ABSInitConfig initConfig,
                                   Name className,
                                   MethodImpl method) {
        super(initConfig);
        this.className = className;
        this.method = method;
        this.classInvariants = repository.getClassInvariants(className.toString());

    }

    @Override
    public void readProblem() throws ProofInputException {

/*        ImmutableSet<Taclet> iinvs =
                collectInterfaceInvariantTaclets(initConfig.getServices()); */

        LocationVariable history = services.getTypeConverter().getHistoryLDT().getHistory();
        LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();

        ABSTermBuilder tb = services.getTermBuilder();

        Term wellFormedHistory = tb.wellFormedHistory(history, services);
        Term wellFormedHeap = tb.wellFormed(heap, services);


        ImmutableSet<Taclet> cinvs =
                getClassInvariantTaclet(className, classInvariants, initConfig.getServices());

        initConfig.setTaclets(initConfig.getTaclets().union(cinvs));

        Function _this = new Function(new Name(tb.newName(services, "this")),
                services.getProgramInfo().getAnyInterfaceSort());
        problemTerm = tb.and(wellFormedHeap, wellFormedHistory, tb.not(tb.equals(tb.func(_this),
                tb.NULL(services))));

        LocationVariable result = new LocationVariable(new ProgramElementName(tb.newName(services, "result")),
                services.getProgramInfo().getKeYJavaType(method.getType().getQualifiedName()));
        LocationVariable future = new LocationVariable(new ProgramElementName(tb.newName(services, "future")),
                services.getProgramInfo().getKeYJavaType("ABS.StdLib.Fut"));


        Pair<ABSStatementBlock, ImmutableList<IProgramVariable>> methodAndParams = services.getProgramInfo().getMethodBody(method);
        ABSMethodFrame frame =
                new ABSMethodFrame(new ABSExecutionContext(
                        new ABSMethodLabel(services.getProgramInfo().getMethodLabelFor(method)),
                        new ABSLocalVariableReference(result), new ABSLocalVariableReference(future)),
                        methodAndParams.first.getBody());

        ABSStatementBlock block = new ABSStatementBlock(frame);

        problemTerm = tb.and(problemTerm, tb.classInvariant(history, heap, _this, services));



        problemTerm = tb.imp(problemTerm, tb.box(JavaBlock.createJavaBlock(block),
                tb.classInvariant(history, heap, _this, services)));

        for (IProgramVariable p : methodAndParams.second) {
            LogicVariable plv = new LogicVariable(new Name(tb.newName(services, p.name().toString())), p.sort());
            problemTerm = tb.all(plv, tb.applyElementary(services, tb.var(p), tb.var(plv), problemTerm));
        }
    }

    @Override
    public ProofAggregate getPO() throws ProofInputException {
        String name = name();
        ProofSettings settings = initConfig.getSettings() != null
                ? initConfig.getSettings()
                : new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
        JavaModel absModel = initConfig.getProofEnv().getJavaModel();
        createProofHeader(absModel.getModelDir(), absModel.getClassPath(), absModel.getBootClassPath());
        return ProofAggregate.createProofAggregate(
                new Proof(name, problemTerm, header, initConfig
                        .createTacletIndex(), initConfig
                        .createBuiltInRuleIndex(), initConfig.getServices(),
                        settings), name);
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
