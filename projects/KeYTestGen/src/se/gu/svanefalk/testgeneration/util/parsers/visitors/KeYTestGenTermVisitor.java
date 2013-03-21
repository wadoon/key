package se.gu.svanefalk.testgeneration.util.parsers.visitors;

import se.gu.svanefalk.testgeneration.util.parsers.TermParserTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;

/**
 * Used to define a custom set of {@link Term} visitors used in KeYTestGen.
 * 
 * @author christopher
 */
public abstract class KeYTestGenTermVisitor implements Visitor {

    @Override
    public void subtreeEntered(final Term subtreeRoot) {
    }

    @Override
    public void subtreeLeft(final Term subtreeRoot) {
    }
}