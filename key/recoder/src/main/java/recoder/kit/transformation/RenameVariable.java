package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Variable;
import recoder.java.ProgramElement;
import recoder.java.declaration.VariableSpecification;
import recoder.java.reference.VariableReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;

import java.util.ArrayList;
import java.util.List;

public class RenameVariable extends TwoPassTransformation {
    private final VariableSpecification vs;

    private final String newName;

    private List<VariableReference> refs;

    public RenameVariable(CrossReferenceServiceConfiguration sc, VariableSpecification vs, String newName) {
        super(sc);
        if (vs == null)
            throw new IllegalArgumentException("Missing variable");
        if (newName == null)
            throw new IllegalArgumentException("Missing name");
        this.vs = vs;
        this.newName = newName;
    }

    public ProblemReport analyze() {
        this.refs = new ArrayList<VariableReference>();
        if (this.newName.equals(this.vs.getName()))
            return setProblemReport(IDENTITY);
        this.refs.addAll(getCrossReferenceSourceInfo().getReferences(this.vs));
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        ProgramFactory pf = getProgramFactory();
        replace(this.vs.getIdentifier(), pf.createIdentifier(this.newName));
        for (int i = this.refs.size() - 1; i >= 0; i--)
            replace(this.refs.get(i).getIdentifier(), pf.createIdentifier(this.newName));
    }
}
