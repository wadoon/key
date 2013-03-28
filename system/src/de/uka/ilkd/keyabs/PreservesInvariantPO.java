package de.uka.ilkd.keyabs;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSStatementBlock;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;

import java.io.IOException;
import java.util.Properties;

/**
 * creates a formula for a given invariant and method which expresses that
 * the method preserves the validity of the invariant, i.e., that if the invariant was valid
 * before execution of the method then the invariant holds again afterwards.
 */
public class PreservesInvariantPO implements IPersistablePO {

    private final ABSClassInvariant invariant;
    private final ABSServices services;
    private final String className;
    private final String methodName;
    private Term problemTerm;
    private final ABSInitConfig initConfig;

    public PreservesInvariantPO(ABSClassInvariant inv,
                                String fullyQualifiedClassName,
                                String methodName,
                                ABSInitConfig initConfig) {
        this.invariant  = inv;
        this.initConfig = initConfig;
        this.services   = initConfig.getServices();
        this.className = fullyQualifiedClassName;
        this.methodName = methodName;
    }

    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
    }

    @Override
    public String name() {
        return "Preserves Invariant";
    }

    @Override
    public void readProblem() throws ProofInputException {
        // get method
        ABSStatementBlock body =
                services.getProgramInfo().getMethodImpl(className, methodName);

        ABSTermBuilder tb = services.getTermBuilder();
        IProgramVariable thisRef = null;
        Term thisT = tb.var(thisRef);
        Term thisNonNull = tb.not(tb.equals(thisT, tb.NULL(services)));

        LocationVariable heap    = services.getTypeConverter().getHeapLDT().getHeap();
        LocationVariable history = services.getTypeConverter().getHistoryLDT().getHistory();

        Term wfHist = tb.wellFormedHistory(history, services);
        Term wfHeap = tb.wellFormed(heap, services);
        Term inv = tb.classInvariant(history, heap, thisRef, services);

        Term pre  = tb.and(thisNonNull, wfHist, wfHeap, inv);

        JavaBlock methodBody = JavaBlock.createJavaBlock(body);

        problemTerm = tb.imp(pre, tb.box(methodBody, inv));

    }

    @Override
    public ProofAggregate getPO() throws ProofInputException {
        final JavaModel javaModel = initConfig.getProofEnv().getJavaModel();
        String header = createProofHeader(javaModel.getModelDir(),
                javaModel.getClassPath(),
                javaModel.getBootClassPath());
        return ProofAggregate.createProofAggregate(new Proof("Preserves Invariant",
                problemTerm,
                header,
                initConfig.createTacletIndex(),
                initConfig.createBuiltInRuleIndex(),
                initConfig.getServices(),
                initConfig.getSettings() != null
                        ? initConfig.getSettings()
                        : new ProofSettings(ProofSettings.DEFAULT_SETTINGS)),
                "Preserves Invariant");
    }


    @Override
    public boolean implies(ProofOblInput po) {
        //TODO: fix
        return po.equals(this);
    }

    private String createProofHeader(String modelDir, String classPath, String bootClassPath) {
        return "";
    }
}