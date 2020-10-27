package recoder.kit.pattern;

import recoder.ModelElement;
import recoder.ModelException;
import recoder.abstraction.Constructor;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

public class Factory implements DesignPattern {
    private final List<FactoryMethod> factoryMethods;

    public Factory(List<FactoryMethod> factoryMethods) {
        this.factoryMethods = factoryMethods;
    }

    public Factory(ClassDeclaration factoryClass, List<TypeDeclaration> products) {
        if (factoryClass == null || products == null)
            throw new NullPointerException();
        int n = products.size();
        this.factoryMethods = new ArrayList<FactoryMethod>(n);
        for (int i = 0; i < n; i++) {
            TypeDeclaration td = products.get(i);
            if (td instanceof ClassDeclaration)
                addFactoryMethods((ClassDeclaration) td);
        }
        ASTList<MethodDeclaration> aSTList = factoryClass.getMembers();
        for (int j = 0; j < this.factoryMethods.size(); j++)
            aSTList.add(this.factoryMethods.get(j).getProducer());
        factoryClass.makeParentRoleValid();
    }

    public void addFactoryMethods(ClassDeclaration decl) {
        List<? extends Constructor> cl = decl.getConstructors();
        for (int i = 0; i < cl.size(); i++) {
            if (cl.get(i) instanceof recoder.abstraction.DefaultConstructor) {
                FactoryMethod m = new FactoryMethod(decl);
                addFactoryMethod(m);
                return;
            }
            ConstructorDeclaration cons = (ConstructorDeclaration) cl.get(i);
            if (cons.isPublic()) {
                FactoryMethod m = new FactoryMethod(cons);
                addFactoryMethod(m);
            }
        }
    }

    public void addFactoryMethod(FactoryMethod m) {
        this.factoryMethods.add(m);
    }

    public List<FactoryMethod> getFactoryMethods() {
        return this.factoryMethods;
    }

    public int getParticipantCount() {
        return (this.factoryMethods != null) ? this.factoryMethods.size() : 0;
    }

    public ModelElement getParticipantAt(int index) {
        if (this.factoryMethods != null)
            return this.factoryMethods.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public void validate() throws ModelException {
        if (this.factoryMethods == null || this.factoryMethods.size() == 0)
            throw new InconsistentPatternException("Factories must contain at least one factory method");
        TypeDeclaration parent = null;
        for (int i = 0, s = this.factoryMethods.size(); i < s; i++) {
            FactoryMethod m = this.factoryMethods.get(i);
            m.validate();
            if (parent == null) {
                parent = m.getProducer().getMemberParent();
            } else if (parent != m.getProducer().getMemberParent()) {
                throw new InconsistentPatternException("Factory methods must be members of the same type");
            }
        }
    }
}
