package de.uka.ilkd.key.java;

import java.util.Collections;
import java.util.Map;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.CCTheoryServices;
import org.key_project.common.core.theories.CCTheory;

import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.util.Debug;

/**
 * This class provides access to the theories.
 * 
 * @author Richard Bubel
 */
public class TheoryServices implements CCTheoryServices {
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

    @Override
    public CCTheory getTheory(Name theoryName) {
        return getLDT(theoryName);
    }

    @Override
    public CCTheory getTheoryFor(Sort sort) {
        return getModelFor(sort);
    }

    @Override
    public Iterable<? extends CCTheory> getTheories() {
        return theories.values();
    }

}