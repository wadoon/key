package recoder.abstraction;

import recoder.service.ProgramModelInfo;

public class PrimitiveType implements Type {
    private final String name;

    private ProgramModelInfo pmi;

    public PrimitiveType(String name, ProgramModelInfo pmi) {
        this.name = name.intern();
        this.pmi = pmi;
    }

    public String getName() {
        return this.name;
    }

    public String getFullName() {
        return this.name;
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.pmi;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.pmi = service;
    }

    public void validate() {
    }

    public PrimitiveType deepClone() {
        throw new UnsupportedOperationException("Cannot deep-clone primitive types");
    }
}
