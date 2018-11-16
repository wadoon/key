package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.logic.Term;

public interface TermNavigator {

    boolean hasNext();

    boolean hasNextSibling();

    Term getCurrentSubterm();

    void gotoNext();

    void gotoNextSibling();

}