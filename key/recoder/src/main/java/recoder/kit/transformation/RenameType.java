package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.ArrayType;
import recoder.abstraction.Constructor;
import recoder.abstraction.Type;
import recoder.java.ProgramElement;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.service.NameInfo;

import java.util.ArrayList;
import java.util.List;

public class RenameType extends TwoPassTransformation {
    private final TypeDeclaration type;

    private final String newName;

    private List<TypeReference> refs;

    private List<? extends Constructor> cons;

    public RenameType(CrossReferenceServiceConfiguration sc, TypeDeclaration type, String newName) {
        super(sc);
        if (type == null)
            throw new IllegalArgumentException("Missing type");
        if (type.getName() == null)
            throw new IllegalArgumentException("May not rename anonymous types");
        if (newName == null)
            throw new IllegalArgumentException("Missing name");
        this.type = type;
        this.newName = newName;
    }

    public ProblemReport analyze() {
        this.refs = new ArrayList<TypeReference>();
        if (this.newName.equals(this.type.getName()))
            return setProblemReport(IDENTITY);
        NameInfo ni = getNameInfo();
        this.refs.addAll(getCrossReferenceSourceInfo().getReferences(this.type));
        this.cons = this.type.getConstructors();
        if (this.cons == null)
            this.cons = new ArrayList<Constructor>(0);
        ArrayType arrayType = ni.getArrayType(this.type);
        while (arrayType != null) {
            this.refs.addAll(getCrossReferenceSourceInfo().getReferences(arrayType));
            arrayType = ni.getArrayType(arrayType);
        }
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        ProgramFactory pf = getProgramFactory();
        replace(this.type.getIdentifier(), pf.createIdentifier(this.newName));
        int i;
        for (i = this.cons.size() - 1; i >= 0; i--) {
            Constructor con = this.cons.get(i);
            if (con instanceof ConstructorDeclaration)
                replace(((ConstructorDeclaration) con).getIdentifier(), pf.createIdentifier(this.newName));
        }
        for (i = this.refs.size() - 1; i >= 0; i--)
            replace(this.refs.get(i).getIdentifier(), pf.createIdentifier(this.newName));
    }
}
