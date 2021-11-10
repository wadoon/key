/**
 *
 */
package recoder.kit.transformation.java5to4.methodRepl;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 *
 * @author Tobias Gutzmann
 *
 */
public class ReplaceOthers extends TwoPassTransformation {
    private List<TypeReference> toRepl;
    private final List<TypeReference> trRepls = new ArrayList<TypeReference>();

    /**
     * This constructor collects the required information by querying the
     * CrossReferenceServiceConfiguration, i.e., all occurrences in
     * the current project are replaced.
     * @param sc
     */
    public ReplaceOthers(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    @Override
    public ProblemReport analyze() {
        ClassType coll = getNameInfo().getClassType("java.lang.StringBuilder");
        if (coll == null) {
            System.out.println("When using ReplaceEmptyCollections, please " +
                    "provide a JDK 1.5 or higher");
            return setProblemReport(IDENTITY);
        }
        toRepl = Collections.unmodifiableList(getServiceConfiguration().getCrossReferenceSourceInfo().getReferences(coll, true));
        for (TypeReference tr : toRepl) {
            trRepls.add(TypeKit.createTypeReference(
                    getProgramFactory(),
                    getNameInfo().getClassType("java.lang.StringBuffer"), tr.getDimensions()));
        }
        if (toRepl.size() == 0)
            return setProblemReport(IDENTITY);
        return setProblemReport(EQUIVALENCE); // hehe
    }

    @Override
    public void transform() {
        super.transform();
        int i = 0;
        for (TypeReference tr : toRepl) {
            replace(tr, trRepls.get(i));
            i++;
        }
        return;
    }

}
