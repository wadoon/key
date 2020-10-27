package recoder.kit.pattern;

import recoder.ModelElement;
import recoder.ModelException;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.convenience.Naming;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.FieldSpecification;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.reference.TypeReference;

public class Property implements DesignPattern {
    private final FieldDeclaration field;

    private final MethodDeclaration getter;

    private final MethodDeclaration setter;

    private MethodDeclaration indexedGetter;

    private MethodDeclaration indexedSetter;

    public Property(FieldDeclaration field) {
        if (field == null)
            throw new NullPointerException();
        this.field = field;
        ProgramFactory factory = field.getFactory();
        TypeReference typeRef = field.getTypeReference();
        String fieldName = field.getVariables().get(0).getName();
        String typeName = typeRef.toString();
        String className = Naming.createClassName(fieldName);
        String source = "public void set" + className + "(" + typeName + " " + fieldName + "){this." + fieldName + "=" + fieldName + ";}";
        try {
            this.setter = factory.parseMethodDeclaration(source);
            source = "public " + typeName + " get" + className + "(){return " + fieldName + ";}";
            this.getter = factory.parseMethodDeclaration(source);
            if (typeRef.getDimensions() > 0) {
                typeName = typeName.substring(0, typeName.length() - 2);
                source = "public void set" + className + "(int index, " + typeName + " " + fieldName + ") { this." + fieldName + "[index] = " + fieldName + "; }";
                this.indexedSetter = factory.parseMethodDeclaration(source);
                source = "public " + typeName + " get" + className + "(int index){return " + fieldName + "[index];}";
                this.indexedGetter = factory.parseMethodDeclaration(source);
            }
        } catch (ParserException pe) {
            throw new IllegalArgumentException("Input obviously made parsing impossible: " + pe);
        }
    }

    public FieldDeclaration getField() {
        return this.field;
    }

    public MethodDeclaration getGetter() {
        return this.getter;
    }

    public MethodDeclaration getSetter() {
        return this.setter;
    }

    public MethodDeclaration getIndexedGetter() {
        return this.getter;
    }

    public MethodDeclaration getIndexedSetter() {
        return this.setter;
    }

    public int getParticipantCount() {
        int res = 0;
        if (this.field != null)
            res++;
        if (this.getter != null)
            res++;
        if (this.setter != null)
            res++;
        if (this.indexedGetter != null)
            res++;
        if (this.indexedSetter != null)
            res++;
        return res;
    }

    public ModelElement getParticipantAt(int index) {
        if (this.field != null) {
            if (index == 0)
                return this.field;
            index--;
        }
        if (this.getter != null) {
            if (index == 0)
                return this.getter;
            index--;
        }
        if (this.setter != null) {
            if (index == 0)
                return this.setter;
            index--;
        }
        if (this.indexedGetter != null) {
            if (index == 0)
                return this.indexedGetter;
            index--;
        }
        if (this.indexedSetter != null &&
                index == 0)
            return this.indexedSetter;
        throw new ArrayIndexOutOfBoundsException();
    }

    public void validate() throws ModelException {
        if (this.setter == null && this.getter == null)
            throw new InconsistentPatternException("Properties must have at least a setter or a getter method");
        String gtype = null, stype = null, ftype = null;
        if (this.getter != null) {
            gtype = this.getter.getReturnType().getName();
        } else {
            stype = this.setter.getParameters().get(0).getTypeReference().getName();
        }
        if (this.field != null)
            ftype = this.field.getTypeReference().getName();
        String btype = (gtype == null) ? stype : gtype;
        if ((stype != null && !btype.equals(stype)) || (gtype != null && !btype.equals(gtype)) || (ftype != null && !btype.equals(ftype)))
            throw new InconsistentPatternException("Property types do not match!");
    }
}
