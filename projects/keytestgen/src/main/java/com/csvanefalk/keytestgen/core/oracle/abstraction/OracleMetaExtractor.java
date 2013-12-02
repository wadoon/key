package com.csvanefalk.keytestgen.core.oracle.abstraction;

import com.csvanefalk.keytestgen.core.oracle.OracleTypeFactory;
import com.csvanefalk.keytestgen.util.parsers.TermParserTools;
import com.csvanefalk.keytestgen.util.visitors.KeYTestGenTermVisitor;
import de.uka.ilkd.key.logic.Term;

/**
 * This visitor is used in order to extract metadata about the poststate of a
 * program, as represented by its postcondition.
 *
 * @author christopher
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