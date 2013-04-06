package de.uka.ilkd.key.proof.init.proofobligations;

import abs.frontend.ast.MethodImpl;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.keyabs.abs.ABSMethodFrame;
import de.uka.ilkd.keyabs.abs.ABSMethodLabel;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSStatementBlock;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSTacletGenerator;
import de.uka.ilkd.keyabs.proof.mgt.ABSSpecificationRepository;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 05.04.1
 * Time: 11:13
 * To change this template use File | Settings | File Templates.
 */
public class ABSPreservesInvariantPO implements ProofOblInput {
    public static final String PRESERVES_INV_PO = "Preserves Invariant";
    private final ABSInitConfig initConfig;
    private final ABSServices services;
    private final ABSSpecificationRepository repository;
    private final Name className;
    private final MethodImpl method;

    private ImmutableSet<ABSClassInvariant> classInvariants;
    private Term problemTerm;
    private String header = null;

    public ABSPreservesInvariantPO(ABSInitConfig initConfig,
                                   Name className,
                                   MethodImpl method) {

        this.initConfig      = initConfig;
        this.services        = initConfig.getServices();
        this.repository      = services.getSpecificationRepository();
        this.classInvariants = repository.getClassInvariants(className.toString());


        this.className = className;
        this.method = method;
    }

    private void createProofHeader(String javaPath,
                                   String classPath,
                                   String bootClassPath) {
        if (header != null) {
            return;
        }
        final StringBuffer sb = new StringBuffer();

        //bootclasspath
        if (bootClassPath != null && !bootClassPath.equals("")) {
            sb.append("\\bootclasspath \"").append(bootClassPath).append(
                    "\";\n\n");
        }

        //classpath
        if (classPath != null && !classPath.equals("")) {
            sb.append("\\classpath \"").append(classPath).append("\";\n\n");
        }

        //javaSource
        sb.append("\\absSource \"").append(javaPath).append("\";\n\n");

        header = sb.toString();
    }

    public ImmutableSet<Taclet> collectInterfaceInvariantTaclets(ABSServices services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
        ABSSpecificationRepository repository = services.getSpecificationRepository();

        for (KeYJavaType type : services.getProgramInfo().getAllKeYJavaTypes()) {
            ImmutableSet<InterfaceInvariant> invs = repository.getInterfaceInvariants(type);
            if (!invs.isEmpty() && type.getJavaType() instanceof ABSInterfaceType) {
                ABSTacletGenerator tg = new ABSTacletGenerator();
                result = result.add(tg.generateTacletForInterfaceInvariant(type, invs, services));
            }
        }
        return result;
    }

    public ImmutableSet<Taclet> getClassInvariantTaclet(ABSServices services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();


        if (!classInvariants.isEmpty()) {
            ABSTacletGenerator tg = new ABSTacletGenerator();
            result = result.add(tg.generateTacletForClassInvariant(className.toString(),
                    classInvariants, services));
        }
        return result;
    }

    @Override
    public String name() {
        return PRESERVES_INV_PO + "_" +
                className + "_" + method.getMethodSig().getName();
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
                getClassInvariantTaclet(initConfig.getServices());

        initConfig.setTaclets(initConfig.getTaclets().union(cinvs));

        Function _this = new Function(new Name(tb.newName(services, "this")), Sort.ANY);
        problemTerm = tb.and(wellFormedHeap, wellFormedHistory, tb.not(tb.equals(tb.func(_this),
                tb.NULL(services))));

        ABSMethodFrame frame =
                new ABSMethodFrame(new ABSMethodLabel(services.getProgramInfo().getMethodLabelFor(method)),
                        services.getProgramInfo().getMethodBody(method).getBody());

        ABSStatementBlock block = new ABSStatementBlock(frame);

        problemTerm = tb.and(problemTerm, tb.classInvariant(history, heap, _this, services));



        problemTerm = tb.imp(problemTerm, tb.box(JavaBlock.createJavaBlock(block),
                tb.classInvariant(history, heap, _this, services)));
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
}
