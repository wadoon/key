package de.uka.ilkd.keyabs.proof.io;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.proof.io.LDTInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.init.ABSInitConfig;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public class ABSLDTInput extends LDTInput<ABSServices, ABSInitConfig> {

    public ABSLDTInput(IKeYFile<ABSServices, ABSInitConfig>[] keyFiles, LDTInput.LDTInputListener listener) {
        super(keyFiles, listener);
    }

    @Override
    protected ImmutableList<LDT> createLDTList(ABSServices services) {
        return ImmutableSLList.<LDT>nil()
                            .prepend(new IntegerLDT(services))
                            .prepend(new BooleanLDT(services))
                            //.prepend(new LocSetLDT(services))
                            //.prepend(new HeapLDT(services))
                            .prepend(new SeqLDT(services))
                            //.prepend(new CharListLDT(services))
                            .prepend(new HistoryLDT(services))
                            ;
    }
    

}
