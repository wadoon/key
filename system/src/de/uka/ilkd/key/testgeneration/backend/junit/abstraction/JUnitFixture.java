package de.uka.ilkd.key.testgeneration.backend.junit.abstraction;

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
     * The declarations in the fixture.
     */
    private final List<JUnitDeclarationStatement> declarations = new LinkedList<JUnitDeclarationStatement>();

    /**
     * The assignment statements
     */
    private final List<JUnitAssignmentStatement> assignments = new LinkedList<JUnitAssignmentStatement>();

    /**
     * Adds a {@link JUnitDeclarationStatement} to the fixture.
     * 
     * @param declarationStatement
     */
    public void addDeclarationStatement(
            JUnitDeclarationStatement declarationStatement) {
        declarations.add(declarationStatement);
    }

    /**
     * Adds a {@link JUnitAssignmentStatement} to the fixture.
     * 
     * @param declarationStatement
     */
    public void addAssignmentStatement(
            JUnitAssignmentStatement assignmentStatement) {
        assignments.add(assignmentStatement);
    }

    /**
     * @return the declarations
     */
    public List<JUnitDeclarationStatement> getDeclarations() {
        return declarations;
    }

    /**
     * @return the assignments
     */
    public List<JUnitAssignmentStatement> getAssignments() {
        return assignments;
    }
}