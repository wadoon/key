package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.ExpressionContainer;
import recoder.java.ProgramElement;
import recoder.java.declaration.Throws;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.service.SourceInfo;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

import java.util.ArrayList;
import java.util.List;

public class RemoveRedundantTypeReferences extends TwoPassTransformation {
    private final List<CompilationUnit> units;

    private final List<TypeReference> references;

    private final boolean removeInterfaces;

    private final boolean removeExceptions;

    private final boolean removeTypeCasts;

    private final ProgressListenerManager listeners = new ProgressListenerManager(this);

    public RemoveRedundantTypeReferences(CrossReferenceServiceConfiguration sc) {
        this(sc, sc.getSourceFileRepository().getCompilationUnits(), true, true, true);
    }

    public RemoveRedundantTypeReferences(CrossReferenceServiceConfiguration sc, List<CompilationUnit> list, boolean removeInterfaces, boolean removeExceptions, boolean removeTypeCasts) {
        super(sc);
        if (list == null)
            throw new IllegalArgumentException("Missing units");
        this.units = list;
        this.references = new ArrayList<TypeReference>();
        this.removeInterfaces = removeInterfaces;
        this.removeExceptions = removeExceptions;
        this.removeTypeCasts = removeTypeCasts;
    }

    public void addProgressListener(ProgressListener l) {
        this.listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        this.listeners.removeProgressListener(l);
    }

    public ProblemReport analyze() {
        SourceInfo si = getSourceInfo();
        this.listeners.fireProgressEvent(0, this.units.size(), "Checking Type References");
        for (int i = 0; i < this.units.size(); i++) {
            TreeWalker tw = new TreeWalker(this.units.get(i));
            while (tw.next()) {
                ProgramElement p = tw.getProgramElement();
                if (this.removeInterfaces && p instanceof TypeDeclaration) {
                    this.references.addAll(TypeKit.getRedundantSuperInterfaces(si, (TypeDeclaration) p));
                    continue;
                }
                if (this.removeExceptions && p instanceof Throws) {
                    this.references.addAll(TypeKit.getRedundantExceptions(si, (Throws) p));
                    continue;
                }
                if (this.removeTypeCasts && p instanceof TypeCast) {
                    TypeCast tc = (TypeCast) p;
                    Type td = si.getType(tc.getTypeReference());
                    Type te = si.getType(tc.getExpressionAt(0));
                    ExpressionContainer parent = tc.getExpressionContainer();
                    if (parent instanceof recoder.java.reference.MethodReference || parent instanceof recoder.java.reference.ConstructorReference || parent instanceof recoder.java.expression.Operator) {
                        if (te == td)
                            this.references.add(tc.getTypeReference());
                        continue;
                    }
                    if (si.isWidening(te, td))
                        this.references.add(tc.getTypeReference());
                }
            }
            this.listeners.fireProgressEvent(i + 1);
        }
        return setProblemReport(this.references.isEmpty() ? IDENTITY : EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        int i;
        for (i = this.references.size() - 1; i >= 0; i--) {
            TypeReference tr = this.references.get(i);
            TypeReferenceContainer con = tr.getParent();
            if (!(con instanceof TypeCast))
                if (con.getChildCount() == 1) {
                    detach(con);
                } else {
                    detach(tr);
                }
        }
        for (i = this.references.size() - 1; i >= 0; i--) {
            TypeReference tr = this.references.get(i);
            TypeReferenceContainer con = tr.getParent();
            if (con instanceof TypeCast) {
                Expression child = ((TypeCast) con).getExpressionAt(0);
                replace(con, child.deepClone());
            }
        }
    }

    public List<TypeReference> getTypeReferenceList() {
        return this.references;
    }

    public List<CompilationUnit> getCompilationUnits() {
        return this.units;
    }
}
