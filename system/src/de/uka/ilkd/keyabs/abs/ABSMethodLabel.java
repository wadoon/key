package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.logic.op.Function;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 06.04.13
 * Time: 14:57
 * To change this template use File | Settings | File Templates.
 */
public class ABSMethodLabel extends ABSProgramElement implements IABSMethodLabel {

    private final Function methodLabel;

    public ABSMethodLabel(Function methodLabel) {
        this.methodLabel = methodLabel;
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSMethodLabel(this);
    }

    @Override
    public String toString() {
        return methodLabel.name().toString();
    }

    public Function getMethodLabel() {
        return methodLabel;
    }
}
