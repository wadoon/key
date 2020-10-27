package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.NamedModelElement;
import recoder.abstraction.ClassType;
import recoder.abstraction.Package;
import recoder.java.ProgramElement;
import recoder.java.reference.PackageReference;
import recoder.kit.*;

import java.util.ArrayList;
import java.util.List;

public class RenamePackage extends TwoPassTransformation {
    private final Package pkg;

    private final String newName;

    private List<PackageReference> refs;

    public RenamePackage(CrossReferenceServiceConfiguration sc, Package pkg, String newName) {
        super(sc);
        if (pkg == null)
            throw new IllegalArgumentException("Missing package");
        if (newName == null)
            throw new IllegalArgumentException("Missing name");
        this.pkg = pkg;
        this.newName = newName;
    }

    public ProblemReport analyze() {
        if (this.newName.equals(this.pkg.getName())) {
            this.refs = new ArrayList<PackageReference>(0);
            return setProblemReport(IDENTITY);
        }
        Package pkg2 = getNameInfo().getPackage(this.newName);
        if (pkg2 != null)
            return setProblemReport(new NameConflict(pkg2));
        List<ClassType> nonTypeDeclarations = PackageKit.getNonSourcePackageTypes(this.pkg);
        if (!nonTypeDeclarations.isEmpty())
            return setProblemReport(new MissingTypeDeclarations(nonTypeDeclarations));
        this.refs = getCrossReferenceSourceInfo().getReferences(this.pkg);
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        Package p = getNameInfo().createPackage(this.newName);
        PackageReference pr = PackageKit.createPackageReference(getProgramFactory(), p);
        for (int i = this.refs.size() - 1; i >= 0; i--) {
            PackageReference ref = this.refs.get(i);
            replace(ref, pr.deepClone());
        }
    }
}
