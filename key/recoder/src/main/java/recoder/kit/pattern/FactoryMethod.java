package recoder.kit.pattern;

import recoder.ModelElement;
import recoder.ModelException;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.kit.MethodKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class FactoryMethod implements DesignPattern {
    private MethodDeclaration producer;

    private ConstructorDeclaration product;

    public FactoryMethod(ConstructorDeclaration product) {
        if (product == null)
            throw new IllegalArgumentException("A factory method requires a product method");
        this.product = product;
        createProducer();
    }

    public FactoryMethod(ClassDeclaration product) {
        if (product == null)
            throw new IllegalArgumentException("A factory method requires a product");
        try {
            this.product = product.getFactory().parseConstructorDeclaration("public " + product.getName() + "(){}");
        } catch (ParserException pe) {
            System.err.println(pe);
        }
        createProducer();
    }

    public MethodDeclaration getProducer() {
        return this.producer;
    }

    public ConstructorDeclaration getProduct() {
        return this.product;
    }

    protected void createProducer() {
        ProgramFactory factory = this.product.getFactory();
        ConstructorDeclaration clone = null;
        try {
            clone = factory.parseConstructorDeclaration(this.product.toSource());
        } catch (ParserException pe) {
            System.err.println(pe);
        }
        Identifier name = clone.getIdentifier();
        this.producer = factory.createMethodDeclaration(clone.getDeclarationSpecifiers(), factory.createTypeReference(name), factory.createIdentifier("create" + name.getText()), clone.getParameters(), clone.getThrown());
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        aSTArrayList.add(factory.createReturn(MethodKit.createNew(clone)));
        this.producer.setBody(factory.createStatementBlock(aSTArrayList));
    }

    public void validate() throws ModelException {
        if (this.producer == null)
            throw new InconsistentPatternException("Factory Method pattern requires a producer");
        if (this.product == null)
            throw new InconsistentPatternException("Factory Method pattern requires a product");
        if (!this.producer.getReturnType().getName().equals(this.product.getMemberParent().getName()))
            throw new InconsistentPatternException("Factory Method producer must create correct product type");
    }

    public int getParticipantCount() {
        int res = 0;
        if (this.producer != null)
            res++;
        if (this.product != null)
            res++;
        return res;
    }

    public ModelElement getParticipantAt(int index) {
        if (this.producer != null) {
            if (index == 0)
                return this.producer;
            index--;
        }
        if (this.product != null &&
                index == 0)
            return this.product;
        throw new ArrayIndexOutOfBoundsException();
    }
}
