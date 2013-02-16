package de.uka.ilkd.key.testgeneration.core.parsers.visitors;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.testgeneration.core.parsers.AbstractTermParser;

/**
 * Used to define a custom set of {@link Term} visitors used in KeYTestGen.
 * 
 * @author christopher
 */
public abstract class KeYTestGenTermVisitor extends AbstractTermParser
        implements Visitor {

    @Override
    public void subtreeEntered(final Term subtreeRoot) {
    }

    @Override
    public void subtreeLeft(final Term subtreeRoot) {
    }
}