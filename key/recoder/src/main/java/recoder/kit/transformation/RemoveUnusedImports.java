package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.Import;
import recoder.java.ProgramElement;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.UnitKit;
import recoder.service.CrossReferenceSourceInfo;
import recoder.util.ProgressListener;
import recoder.util.ProgressListenerManager;

import java.util.ArrayList;
import java.util.List;

public class RemoveUnusedImports extends TwoPassTransformation {
    private final List<CompilationUnit> units;

    private final List<Import> imports;

    private final ProgressListenerManager listeners = new ProgressListenerManager(this);

    public RemoveUnusedImports(CrossReferenceServiceConfiguration sc) {
        this(sc, sc.getSourceFileRepository().getCompilationUnits());
    }

    public RemoveUnusedImports(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        ArrayList<CompilationUnit> al = new ArrayList<CompilationUnit>(1);
        al.add(cu);
        this.units = al;
        this.imports = new ArrayList<Import>();
    }

    public RemoveUnusedImports(CrossReferenceServiceConfiguration sc, List<CompilationUnit> list) {
        super(sc);
        if (list == null)
            throw new IllegalArgumentException("Missing units");
        this.units = list;
        this.imports = new ArrayList<Import>();
    }

    public void addProgressListener(ProgressListener l) {
        this.listeners.addProgressListener(l);
    }

    public void removeProgressListener(ProgressListener l) {
        this.listeners.removeProgressListener(l);
    }

    public ProblemReport analyze() {
        this.listeners.fireProgressEvent(0, this.units.size(), "Checking Imports");
        CrossReferenceSourceInfo xrsi = getCrossReferenceSourceInfo();
        for (int i = 0; i < this.units.size(); i++) {
            this.imports.addAll(UnitKit.getUnnecessaryImports(xrsi, this.units.get(i)));
            this.listeners.fireProgressEvent(i + 1);
        }
        return setProblemReport(this.imports.isEmpty() ? IDENTITY : EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        for (int i = this.imports.size() - 1; i >= 0; i--)
            detach(this.imports.get(i));
    }

    public List<Import> getImportList() {
        return this.imports;
    }

    public List<CompilationUnit> getCompilationUnits() {
        return this.units;
    }
}
