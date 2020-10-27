package recoder.service;

import recoder.ModelException;
import recoder.abstraction.ClassType;
import recoder.java.Import;

import java.util.ArrayList;
import java.util.List;

public class AmbiguousImportException extends ModelException {
    private static final long serialVersionUID = 699763267768804228L;

    private final Import importStatement;

    private final ClassType version1;

    private final ClassType version2;

    public AmbiguousImportException(Import importStatement, ClassType version1, ClassType version2) {
        this.importStatement = importStatement;
        this.version1 = version1;
        this.version2 = version2;
    }

    public AmbiguousImportException(String s, Import importStatement, ClassType version1, ClassType version2) {
        super(s);
        this.importStatement = importStatement;
        this.version1 = version1;
        this.version2 = version2;
    }

    public Import getAmbiguousImport() {
        return this.importStatement;
    }

    public List<ClassType> getChoices() {
        List<ClassType> list = new ArrayList<ClassType>(2);
        list.add(this.version1);
        list.add(this.version2);
        return list;
    }
}
