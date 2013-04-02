package de.uka.ilkd.keyabs.proof.io;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.proof.io.LDTInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.logic.ldt.HeapLDT;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;
import de.uka.ilkd.keyabs.logic.ldt.LocSetLDT;

public class ABSLDTInput extends LDTInput<ABSServices, ABSInitConfig> {

    public ABSLDTInput(IKeYFile<ABSServices, ABSInitConfig>[] keyFiles, LDTInput.LDTInputListener listener) {
        super(keyFiles, listener);
    }

    @Override
    protected ImmutableList<LDT> createLDTList(ABSServices services) {
        return ImmutableSLList.<LDT>nil()
                            .prepend(new IntegerLDT(services))
                            .prepend(new BooleanLDT(services))
                            .prepend(new LocSetLDT(services))
                            .prepend(new HeapLDT(services))
                            .prepend(new SeqLDT(services))
                            .prepend(new FreeLDT(services))
                            .prepend(new HistoryLDT(services))
                            ;
    }
}
