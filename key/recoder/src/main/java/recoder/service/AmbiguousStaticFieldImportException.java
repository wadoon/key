package recoder.service;

import recoder.ModelException;
import recoder.abstraction.Field;
import recoder.abstraction.Variable;
import recoder.java.Import;

import java.util.ArrayList;
import java.util.List;

public class AmbiguousStaticFieldImportException extends ModelException {
    private static final long serialVersionUID = -2587328246662978766L;

    private final Import importStatement1;

    private final Import importStatement2;

    private final Variable version1;

    private final Variable version2;

    public AmbiguousStaticFieldImportException(Import importStatement1, Import importStatement2, Variable version1, Variable version2) {
        this.importStatement1 = importStatement1;
        this.importStatement2 = importStatement2;
        this.version1 = version1;
        this.version2 = version2;
    }

    public AmbiguousStaticFieldImportException(String s, Import importStatement1, Import importStatement2, Field version1, Field version2) {
        super(s);
        this.importStatement1 = importStatement1;
        this.importStatement2 = importStatement2;
        this.version1 = version1;
        this.version2 = version2;
    }

    public List<Import> getAmbiguousImports() {
        List<Import> list = new ArrayList<Import>(2);
        list.add(this.importStatement1);
        list.add(this.importStatement2);
        return list;
    }

    public List<Variable> getChoices() {
        List<Variable> list = new ArrayList<Variable>(2);
        list.add(this.version1);
        list.add(this.version2);
        return list;
    }
}
