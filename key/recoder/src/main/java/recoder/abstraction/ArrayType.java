package recoder.abstraction;

import recoder.bytecode.MethodInfo;
import recoder.service.ProgramModelInfo;

public class ArrayType implements Type {
    ProgramModelInfo pmi;
    private final Type basetype;
    private String shortName;
    private String fullName;

    public ArrayType(Type basetype, ProgramModelInfo pmi) {
        this.basetype = basetype;
        this.pmi = pmi;
        makeNames();
    }

    public void makeNames() {
        this.shortName = this.basetype.getName() + "[]";
        this.fullName = this.basetype.getFullName() + "[]";
    }

    public Type getBaseType() {
        return this.basetype;
    }

    public String getName() {
        return this.shortName;
    }

    public String getFullName() {
        return this.fullName;
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.pmi;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.pmi = service;
    }

    public void validate() {
    }

    public MethodInfo deepClone() {
        throw new UnsupportedOperationException("Cannot deep-clone implicit information");
    }
}
