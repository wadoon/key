package de.uka.ilkd.key.strategy.conflictbasedinst;

import java.util.Stack;

import de.uka.ilkd.key.logic.Term;

public class ConflictFindingInstantiatior {

    private Stack<Operands> opStack;

    public ConflictFindingInstantiatior(Term formula, MatchingConstraints mc) {
        opStack = new Stack<ConflictFindingInstantiatior.Operands>();
    }

    private class Operands {
        private Term formula;
        private boolean polarity;
        private ConstrainedAssignment ca;
        private MatchingConstraints mc;
    }

}
