package recoder.kit;

import recoder.CrossReferenceServiceConfiguration;

public abstract class TwoPassTransformation extends Transformation {
    protected TwoPassTransformation() {
    }

    public TwoPassTransformation(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    public ProblemReport analyze() {
        setProblemReport(NO_PROBLEM);
        return NO_PROBLEM;
    }

    public void transform() {
        if (getProblemReport() == null)
            throw new IllegalStateException("No analyze");
        if (isVisible())
            getChangeHistory().begin(this);
    }

    public ProblemReport execute() {
        ProblemReport report = analyze();
        if (report instanceof NoProblem && !(report instanceof Identity))
            transform();
        return report;
    }
}
