package recoder.java.declaration;

import recoder.abstraction.ElementValuePair;
import recoder.java.*;
import recoder.java.expression.Literal;
import recoder.java.reference.AnnotationPropertyReference;

public class AnnotationElementValuePair extends JavaNonTerminalProgramElement implements ExpressionContainer, ElementValuePair {
    private static final long serialVersionUID = -8603363313540445285L;

    protected AnnotationUseSpecification parent;

    protected AnnotationPropertyReference element;

    protected Expression elementValue;

    public AnnotationElementValuePair() {
    }

    public AnnotationElementValuePair(AnnotationPropertyReference elem, Expression elementValue) {
        this.element = elem;
        this.elementValue = elementValue;
    }

    protected AnnotationElementValuePair(AnnotationElementValuePair proto) {
        super(proto);
        this.element = proto.element.deepClone();
        this.elementValue = proto.elementValue.deepClone();
        makeParentRoleValid();
    }

    static Object expressionToJavaObject(Expression expr) {
        if (expr instanceof Literal)
            return ((Literal) expr).getEquivalentJavaType();
        throw new RuntimeException("Do not understand type of expression in AnnotationElementValuePair.getValue()... (TODO)");
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.element != null)
            this.element.setParent(this);
        if (this.elementValue != null)
            this.elementValue.setExpressionContainer(this);
    }

    public int getChildCount() {
        int res = 0;
        if (this.element != null)
            res++;
        if (this.elementValue != null)
            res++;
        return res;
    }

    public ProgramElement getChildAt(int index) {
        int i = index;
        if (this.element != null) {
            if (i == 0)
                return this.element;
            i--;
        }
        if (this.elementValue != null) {
            if (i == 0)
                return this.elementValue;
            i--;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public SourceElement getFirstElement() {
        return (this.element != null) ? this.element.getFirstElement() : ((this.elementValue != null) ? this.elementValue.getFirstElement() : this);
    }

    public SourceElement getLastElement() {
        return (this.elementValue != null) ? this.elementValue.getLastElement() : ((this.element != null) ? this.element.getLastElement() : this);
    }

    public int getChildPositionCode(ProgramElement child) {
        if (child == this.element)
            return 0;
        if (child == this.elementValue)
            return 1;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (p == this.element) {
            this.element = (AnnotationPropertyReference) q;
            if (this.element != null)
                this.element.setParent(this);
            return true;
        }
        if (p == this.elementValue) {
            this.elementValue = (Expression) q;
            if (this.elementValue != null)
                this.elementValue.setExpressionContainer(this);
            return true;
        }
        return false;
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public void accept(SourceVisitor v) {
        v.visitElementValuePair(this);
    }

    public AnnotationElementValuePair deepClone() {
        return new AnnotationElementValuePair(this);
    }

    public Expression getElementValue() {
        return this.elementValue;
    }

    public void setElementValue(Expression elementValue) {
        this.elementValue = elementValue;
    }

    public AnnotationPropertyReference getElement() {
        return this.element;
    }

    public void setElement(AnnotationPropertyReference ref) {
        this.element = ref;
    }

    public int getExpressionCount() {
        return (this.elementValue == null) ? 0 : 1;
    }

    public Expression getExpressionAt(int index) {
        if (index == 0 && this.elementValue != null)
            return this.elementValue;
        throw new ArrayIndexOutOfBoundsException(index);
    }

    public AnnotationUseSpecification getParent() {
        return this.parent;
    }

    public void setParent(AnnotationUseSpecification parent) {
        this.parent = parent;
    }

    public Object getValue() {
        return expressionToJavaObject(this.elementValue);
    }

    public String getElementName() {
        if (this.element == null)
            return "(default value)";
        return this.element.getIdentifier().getText();
    }
}
