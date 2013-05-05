package se.gu.svanefalk.testgeneration.backend.junit.abstraction;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents a JUnit test fixture. It consists of a set of variable
 * declarations, as well as a set of field assignments.
 * 
 * @author christopher
 * 
 */
public class JUnitFixture {

    /**
     * The assignment assertions
     */
    private final List<JUnitAssignmentStatement> assignments = new LinkedList<JUnitAssignmentStatement>();

    /**
     * The declarations in the fixture.
     */
    private final List<JUnitDeclarationStatement> declarations = new LinkedList<JUnitDeclarationStatement>();

    /**
     * Adds a {@link JUnitAssignmentStatement} to the fixture.
     * 
     * @param declarationStatement
     */
    public void addAssignmentStatement(
            final JUnitAssignmentStatement assignmentStatement) {
        assignments.add(assignmentStatement);
    }

    /**
     * Adds a {@link JUnitDeclarationStatement} to the fixture.
     * 
     * @param declarationStatement
     */
    public void addDeclarationStatement(
            final JUnitDeclarationStatement declarationStatement) {
        declarations.add(declarationStatement);
    }

    /**
     * @return the assignments
     */
    public List<JUnitAssignmentStatement> getAssignments() {
        return assignments;
    }

    /**
     * @return the declarations
     */
    public List<JUnitDeclarationStatement> getDeclarations() {
        return declarations;
    }
}