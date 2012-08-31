package de.uka.ilkd.keyabs.abs;

import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.Model;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.IProgramInfo;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.abs.converter.ABSModelParserInfo;
import de.uka.ilkd.keyabs.init.SortBuilder;

public class ABSInfo implements IProgramInfo {

    private final ABSServices services;

    /**
     * maps ABS type declarations to KeYABSTypes (ok at the moment KeYJavaTypes)
     */
    private final KeYABSMapping program2key;

    /**
     * the ABS model
     */
    private final ABSModelParserInfo absInfo;

    /**
     * hashmap for all known (logic sort, abs type) pairs
     */
    private final HashMap<String, KeYJavaType> name2sortABSPair = new HashMap<String, KeYJavaType>();

    public ABSInfo(ABSServices services) {
        this(services, new KeYABSMapping());
    }

    public ABSInfo(ABSServices services, KeYABSMapping program2key) {
        this(services, program2key, new ABSModelParserInfo());
    }

    ABSInfo(ABSServices services, KeYABSMapping program2key,
            ABSModelParserInfo absInfo) {
        this.services = services;
        this.program2key = program2key;
        this.absInfo = absInfo;
    }

    @Override
    public IProgramInfo copy(IServices serv) {
        return new ABSInfo((ABSServices) serv, program2key.copy(), absInfo);
    }

    public ABSModelParserInfo getABSParserInfo() {
        return absInfo;
    }

    @Override
    public Set<KeYJavaType> getAllKeYJavaTypes() {
        ensureValidCache();
        final HashSet<KeYJavaType> set = new HashSet<KeYJavaType>();
        set.addAll(name2sortABSPair.values());
        return Collections.unmodifiableSet(set);
    }

    @Override
    public ImmutableList<IProgramMethod> getAllProgramMethods(KeYJavaType kjt) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableList<IProgramMethod> getAllProgramMethodsLocallyDeclared(
            KeYJavaType kjt) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableList<KeYJavaType> getAllSubtypes(KeYJavaType type) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableList<KeYJavaType> getAllSupertypes(KeYJavaType type) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ImmutableList<KeYJavaType> getCommonSubtypes(KeYJavaType k1,
            KeYJavaType k2) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ExecutionContext getDefaultExecutionContext() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getFullName(KeYJavaType t) {
        return t.getFullName();
    }

    @Override
    public IObserverFunction getInv() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getKeYJavaType(Sort sort) {
        return getTypeByName(sort.name().toString());
    }

    @Override
    public KeYJavaType getKeYJavaType(String fullName) {
        return getTypeByName(fullName);
    }

    @Override
    public KeYJavaType getKeYJavaType(Type t) {
        return getTypeByName(t.getFullName());
    }

    @Override
    public KeYJavaType getKeYJavaTypeByClassName(String className) {
        return getTypeByName(className);
    }

    @Override
    public ABSServices getServices() {
        return services;
    }

    @Override
    public KeYJavaType getTypeByClassName(String className) {
        return getTypeByName(className);
    }

    @Override
    public KeYJavaType getTypeByName(String fullName) {
        ensureValidCache();
        return name2sortABSPair.get(fullName);
    }

    @Override
    public boolean isInterface(KeYJavaType t) {
        return t.getJavaType() instanceof ABSInterfaceType;
    }

    @Override
    public boolean isReferenceSort(Sort sort) {
        return sort.extendsTrans(services.getNamespaces().sorts().lookup(SortBuilder.ABS_ANY_INTERFACE_SORT_NAME));
    }

    @Override
    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        return subType.getSort().extendsTrans(superType.getSort());
    }

    @Override
    public Sort nullSort() {
        return services.getNamespaces().sorts().lookup(NullSort.NAME);
    }

    @Override
    public KeYABSMapping rec2key() {
        return program2key;
    }

    private void buildNameCache() {
        name2sortABSPair.clear();
        for (Object _sortABS : rec2key().elemsKeY()) {
            KeYJavaType sortABS = (KeYJavaType) _sortABS;
            name2sortABSPair.put(sortABS.getFullName(), sortABS);
        }
    }

    private void ensureValidCache() {
        if (name2sortABSPair.size() != rec2key().size()) {
            buildNameCache();
        }
    }

    public CoreAbsBackend getCoreABSBackend() {
        return absInfo.getABSBackend();
    }

    public Model parseInContext(String s) throws IOException {
        return absInfo.parseInContext(s);
    }
}
