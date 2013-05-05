package se.gu.svanefalk.testgeneration.core.oracle.abstraction;

import se.gu.svanefalk.testgeneration.core.oracle.OracleTypeFactory;
import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import se.gu.svanefalk.testgeneration.util.parsers.visitors.KeYTestGenTermVisitor;
import de.uka.ilkd.key.logic.Term;

/**
 * This visitor is used in order to extract metadata about the poststate of a
 * program, as represented by its postcondition.
 * 
 * @author christopher
 * 
 */
public class OracleMetaExtractor extends KeYTestGenTermVisitor {

    /**
     * The exception which should be thrown by the method under test, if any.
     */
    OracleType thrownException = null;

    /**
     * @return the exception thrown by the method under test.
     */
    public OracleType getThrownException() {
        return thrownException;
    }

    /**
     * Walk the {@link Term} corresponding to the postcondition, and extract the
     * required metadata.
     */
    @Override
    public void visit(final Term visited) {

        if (TermParserTools.isLocationVariable(visited)) {

            /*
             * Remove the exception check introduced by KeY
             */
            final String variableName = visited.op().name().toString();
            if (variableName.equals("exc")) {
                thrownException = OracleTypeFactory.getOracleType(visited);
            }
        }
    }
}