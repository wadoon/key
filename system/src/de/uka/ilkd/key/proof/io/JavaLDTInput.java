package de.uka.ilkd.key.proof.io;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.proof.init.InitConfig;

public class JavaLDTInput extends LDTInput<Services, InitConfig> {

    public JavaLDTInput(IKeYFile<Services, InitConfig>[] keyFiles, LDTInputListener listener) {
        super(keyFiles, listener);
    }

    @Override
    protected ImmutableList<LDT> createLDTList(Services services) {
        return ImmutableSLList.<LDT>nil()
                .prepend(new IntegerLDT(services))
                .prepend(new BooleanLDT(services))
                .prepend(new LocSetLDT(services))
                .prepend(new HeapLDT(services))
                .prepend(new SeqLDT(services))
                .prepend(new CharListLDT(services));
    }

}
