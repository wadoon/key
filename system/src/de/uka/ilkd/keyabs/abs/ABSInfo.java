package de.uka.ilkd.keyabs.abs;

import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.IProgramInfo;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.KeYRecoderMapping;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;

public class ABSInfo implements IProgramInfo {

    @Override
    public KeYRecoderMapping rec2key() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IProgramInfo copy(IServices serv) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IServices getServices() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String getFullName(KeYJavaType t) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getTypeByName(String fullName) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getTypeByClassName(String className) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Set<KeYJavaType> getAllKeYJavaTypes() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getKeYJavaType(String fullName) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getKeYJavaTypeByClassName(String className) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean isSubtype(KeYJavaType subType, KeYJavaType superType) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean isInterface(KeYJavaType t) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public KeYJavaType getKeYJavaType(Sort sort) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public KeYJavaType getKeYJavaType(Type t) {
        // TODO Auto-generated method stub
        return null;
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
    public Sort nullSort() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ExecutionContext getDefaultExecutionContext() {
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
    public IObserverFunction getInv() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean isReferenceSort(Sort sort) {
        // TODO Auto-generated method stub
        return false;
    }

}
