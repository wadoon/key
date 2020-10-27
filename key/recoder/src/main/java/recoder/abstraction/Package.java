package recoder.abstraction;

import recoder.ModelException;
import recoder.bytecode.ClassFile;
import recoder.java.CompilationUnit;
import recoder.service.ProgramModelInfo;
import recoder.util.Debug;

import java.util.List;

public class Package implements ClassTypeContainer {
    private final String name;

    private ProgramModelInfo pmi;

    public Package(String name, ProgramModelInfo pmi) {
        Debug.assertNonnull(name);
        this.name = name;
        this.pmi = pmi;
    }

    public String getName() {
        return this.name;
    }

    public String getFullName() {
        return getName();
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.pmi;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.pmi = service;
    }

    public List<? extends ClassType> getTypes() {
        return this.pmi.getTypes(this);
    }

    public List<? extends AnnotationUse> getPackageAnnotations() {
        CompilationUnit cl = this.pmi.getServiceConfiguration().getSourceFileRepository().getCompilationUnit(getFullName() + ".package-info");
        if (cl != null)
            return cl.getPackageSpecification().getAnnotations();
        ClassFile cf = this.pmi.getServiceConfiguration().getClassFileRepository().getClassFile(getFullName() + ".package-info");
        if (cf != null)
            return cf.getAnnotations();
        throw new UnsupportedOperationException();
    }

    public ClassTypeContainer getContainer() {
        return null;
    }

    public Package getPackage() {
        return this;
    }

    public void validate() throws ModelException {
    }
}
