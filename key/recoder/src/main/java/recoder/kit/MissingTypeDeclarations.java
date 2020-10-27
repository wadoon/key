package recoder.kit;

import recoder.abstraction.ClassType;

import java.util.List;

public class MissingTypeDeclarations extends MissingSources {
    private static final long serialVersionUID = 6106584488830182556L;

    private final List<ClassType> nonTypeDeclarations;

    public MissingTypeDeclarations(List<ClassType> nonTypeDeclarations) {
        this.nonTypeDeclarations = nonTypeDeclarations;
    }

    public List<ClassType> getNonTypeDeclarations() {
        return this.nonTypeDeclarations;
    }
}
