package de.uka.ilkd.keyabs.abs;


public abstract class ABSBinaryOperatorPureExp extends ABSNonTerminalProgramElement implements IABSPureExpression {

    private final IABSPureExpression left;
    private final IABSPureExpression right;
    
    public ABSBinaryOperatorPureExp(IABSPureExpression left,
            IABSPureExpression right) {
        super();
        this.left = left;
        this.right = right;
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public IABSPureExpression getChildAt(int index) {
        switch (index) {
        case 0: return left;
        case 1: return right;
        default: throw new IndexOutOfBoundsException();
        }
    }
    
    
}
