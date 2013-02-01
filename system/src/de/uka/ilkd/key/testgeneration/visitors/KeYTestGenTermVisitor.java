package de.uka.ilkd.key.testgeneration.visitors;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.testgeneration.parsers.AbstractTermParser;

/**
 * Used to define a custom set of {@link Term} visitors used in KeYTestGen.
 * 
 * @author christopher
 */
public abstract class KeYTestGenTermVisitor extends AbstractTermParser
        implements Visitor {

    @Override
    public void subtreeEntered(Term subtreeRoot) {
    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {
    }
}