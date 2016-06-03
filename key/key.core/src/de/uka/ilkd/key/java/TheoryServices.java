package de.uka.ilkd.key.java;

import java.util.Collections;
import java.util.Map;

import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.MapLDT;
import de.uka.ilkd.key.ldt.PermissionLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/**
 * This class provides access to the theories.
 * 
 * @author Richard Bubel
 */
public class TheoryServices {
    // Maps LDT names to LDT instances.
    private Map<Name, LDT> theories;

    public TheoryServices() {
        theories = Collections.emptyMap();
    }

    /**
     * initializes this service by copying the content of {@code theoryServices}
     * @param theoryServices the {@link TheoryServices} to copy
     */
    void init(TheoryServices theoryServices) {
        this.theories = Collections.unmodifiableMap(theoryServices.theories);
    }

    /**
     * populates this service by fresh LDTS obtained from {@link LDT#getNewLDTInstances(Services)}
     * @param theoryServices the {@link Services} 
     */
    public void init(Services services) {
        theories = Collections.unmodifiableMap(LDT.getNewLDTInstances(services));
    }
    
    public BooleanLDT getBooleanLDT() {
        return (BooleanLDT) getLDT(BooleanLDT.NAME);
    }

    public CharListLDT getCharListLDT() {
        return (CharListLDT) getLDT(CharListLDT.NAME);
    }

    public HeapLDT getHeapLDT() {
        return (HeapLDT) getLDT(HeapLDT.NAME);
    }

    public IntegerLDT getIntegerLDT() {
        return (IntegerLDT) getLDT(IntegerLDT.NAME);
    }

    public LocSetLDT getLocSetLDT() {
        return (LocSetLDT) getLDT(LocSetLDT.NAME);
    }

    public MapLDT getMapLDT() {
        return (MapLDT) getLDT(MapLDT.NAME);
    }
    
    public PermissionLDT getPermissionLDT() {
        return (PermissionLDT) getLDT(PermissionLDT.NAME);
    }

    public SeqLDT getSeqLDT() {
        return (SeqLDT) getLDT(SeqLDT.NAME);
    }

    LDT getLDT(Name ldtName) {
        return theories.get(ldtName);
    }

    public LDT getModelFor(Sort s) {
    for(final LDT ldt : theories.values()) {
        if(s.equals(ldt.targetSort())) {
    	return ldt;
        }
    }
        Debug.out("No LDT found for ", s);
        return null;
    }

    public Iterable<LDT> getModels() {
        return theories.values();
    }

}