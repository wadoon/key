package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Method;
import recoder.java.ProgramElement;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.kit.MethodKit;
import recoder.kit.MissingSources;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.service.CrossReferenceSourceInfo;

import java.util.ArrayList;
import java.util.List;

public class RenameMethod extends TwoPassTransformation {
    private final Method methodToRename;

    private final String newName;

    private List<MethodDeclaration> methods;

    private List<MethodReference> refs;

    public RenameMethod(CrossReferenceServiceConfiguration sc, MethodDeclaration method, String newName) {
        super(sc);
        if (method == null)
            throw new IllegalArgumentException("Missing method");
        if (newName == null)
            throw new IllegalArgumentException("Missing name");
        this.methodToRename = method;
        this.newName = newName;
    }

    public ProblemReport analyze() {
        if (this.newName.equals(this.methodToRename.getName()))
            return setProblemReport(IDENTITY);
        CrossReferenceSourceInfo xr = getCrossReferenceSourceInfo();
        this.methods = new ArrayList<MethodDeclaration>();
        List<Method> relatedMethods = MethodKit.getAllRelatedMethods(xr, this.methodToRename);
        List<Method> problems = null;
        for (int i = relatedMethods.size() - 1; i >= 0; i--) {
            Method m = relatedMethods.get(i);
            if (m instanceof MethodDeclaration) {
                this.methods.add((MethodDeclaration) m);
            } else {
                if (problems == null)
                    problems = new ArrayList<Method>();
                problems.add(m);
            }
        }
        if (problems != null)
            return setProblemReport(new MissingMethodDeclarations(problems));
        this.refs = new ArrayList<MethodReference>();
        for (int j = this.methods.size() - 1; j >= 0; j--) {
            MethodDeclaration mdecl = this.methods.get(j);
            List<MemberReference> mrefs = xr.getReferences(mdecl);
            for (int k = 0, s = mrefs.size(); k < s; k++) {
                MemberReference mr = mrefs.get(k);
                if (mr instanceof MethodReference)
                    this.refs.add((MethodReference) mr);
            }
        }
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        ProgramFactory pf = getProgramFactory();
        int i;
        for (i = this.methods.size() - 1; i >= 0; i--)
            replace(this.methods.get(i).getIdentifier(), pf.createIdentifier(this.newName));
        for (i = this.refs.size() - 1; i >= 0; i--)
            replace(this.refs.get(i).getIdentifier(), pf.createIdentifier(this.newName));
    }

    public List<MethodDeclaration> getRenamedMethods() {
        return this.methods;
    }

    public static class MissingMethodDeclarations extends MissingSources {
        private static final long serialVersionUID = 9214788084198236635L;

        private final List<Method> nonMethodDeclarations;

        MissingMethodDeclarations(List<Method> nonMethodDeclarations) {
            this.nonMethodDeclarations = nonMethodDeclarations;
        }

        public List<Method> getNonMethodDeclarations() {
            return this.nonMethodDeclarations;
        }
    }
}
