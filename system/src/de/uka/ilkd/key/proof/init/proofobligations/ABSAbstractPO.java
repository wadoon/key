package de.uka.ilkd.key.proof.init.proofobligations;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSTacletGenerator;
import de.uka.ilkd.keyabs.proof.mgt.ABSSpecificationRepository;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 07.04.13
 * Time: 04:24
 * To change this template use File | Settings | File Templates.
 */
public abstract class ABSAbstractPO implements ProofOblInput {
    protected final ABSInitConfig initConfig;
    protected final ABSServices services;
    protected final ABSSpecificationRepository repository;
    protected Term problemTerm;
    protected String header = null;

    public ABSAbstractPO(ABSInitConfig initConfig) {
        this.initConfig      = initConfig;
        this.services        = initConfig.getServices();
        this.repository      = services.getSpecificationRepository();
    }

    protected void createProofHeader(String javaPath,
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

    public ImmutableSet<Taclet> getClassInvariantTaclet(Name className,
                                                        ImmutableSet<ABSClassInvariant> classInvariants,
            ABSServices services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();


        if (!classInvariants.isEmpty()) {
            ABSTacletGenerator tg = new ABSTacletGenerator();
            result = result.add(tg.generateTacletForClassInvariant(className.toString(),
                    classInvariants, services));
        }
        return result;
    }


}
