package recoder.kit;

import recoder.ProgramFactory;
import recoder.abstraction.ClassType;
import recoder.abstraction.Package;
import recoder.java.NamedProgramElement;
import recoder.java.reference.PackageReference;
import recoder.service.ChangeHistory;
import recoder.service.CrossReferenceSourceInfo;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

public class PackageKit {
    public static PackageReference createPackageReference(ProgramFactory f, Package p) {
        PackageReference result = null;
        String name = p.getFullName();
        if (name.equals(""))
            return null;
        int j = -1;
        while (true) {
            int i = j + 1;
            j = name.indexOf(".", i);
            String token = (j > i) ? name.substring(i, j) : name.substring(i);
            result = f.createPackageReference(result, f.createIdentifier(token));
            if (j <= i)
                return result;
        }
    }

    public static List<ClassType> getNonSourcePackageTypes(Package pkg) {
        List<ClassType> result = new ArrayList<ClassType>();
        List<? extends ClassType> classes = pkg.getTypes();
        for (int i = classes.size() - 1; i >= 0; i--) {
            ClassType ct = classes.get(i);
            if (!(ct instanceof recoder.java.declaration.TypeDeclaration))
                result.add(ct);
        }
        return result;
    }

    public static boolean rename(ChangeHistory ch, CrossReferenceSourceInfo xr, Package pkg, String newName) {
        Debug.assertNonnull(xr, pkg, newName);
        Debug.assertNonnull(pkg.getName());
        if (!newName.equals(pkg.getName())) {
            List<PackageReference> refs = xr.getReferences(pkg);
            for (int i = refs.size() - 1; i >= 0; i--)
                MiscKit.rename(ch, refs.get(i), newName);
            return true;
        }
        return false;
    }
}
