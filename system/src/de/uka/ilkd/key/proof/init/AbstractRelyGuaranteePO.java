package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.speclang.ThreadSpecification;


public abstract class AbstractRelyGuaranteePO extends AbstractPO {

    private final static String THREAD = "java.lang.Thread";
    protected final ThreadSpecification tspec;
    
    public AbstractRelyGuaranteePO (InitConfig initConfig, String name, ThreadSpecification tspec) {
        super(initConfig, name);
        final KeYJavaType threadType = javaInfo.getTypeByClassName(THREAD);
        if (! javaInfo.isSubtype(tspec.getKJT(), threadType))
            throw new IllegalArgumentException("Thread specification must be associated to a subtype of java.lang.Thread");
        this.tspec = tspec;
    }

    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return environmentConfig;
    }
    
}
