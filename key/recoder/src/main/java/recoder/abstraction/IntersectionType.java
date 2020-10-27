package recoder.abstraction;

import recoder.ModelException;
import recoder.service.ProgramModelInfo;

import java.util.ArrayList;
import java.util.List;

public class IntersectionType implements ClassType {
    private final List<Type> types;

    private ProgramModelInfo pmi;

    public IntersectionType(List<Type> types, ProgramModelInfo pmi) {
        this.types = types;
        this.pmi = pmi;
    }

    public String getFullName() {
        StringBuffer res = new StringBuffer();
        for (int i = 0; i < this.types.size(); i++) {
            if (i != 0)
                res.append(" & ");
            res.append(this.types.get(i).getFullName());
        }
        return res.toString();
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.pmi;
    }

    public void setProgramModelInfo(ProgramModelInfo pmi) {
        this.pmi = pmi;
    }

    public String getName() {
        StringBuffer res = new StringBuffer();
        for (int i = 0; i < this.types.size(); i++) {
            if (i != 0)
                res.append(" & ");
            res.append(this.types.get(i).getName());
        }
        return res.toString();
    }

    public void validate() throws ModelException {
    }

    public boolean isInterface() {
        return false;
    }

    public boolean isOrdinaryInterface() {
        return false;
    }

    public boolean isAnnotationType() {
        return false;
    }

    public boolean isEnumType() {
        return false;
    }

    public boolean isOrdinaryClass() {
        return false;
    }

    public boolean isAbstract() {
        return true;
    }

    public List<ClassType> getSupertypes() {
        List<ClassType> res = new ArrayList<ClassType>();
        boolean addedObject = false;
        for (int i = 0; i < this.types.size(); i++) {
            Type t = this.types.get(i);
            if (t instanceof ClassType) {
                res.add((ClassType) t);
                if (t.getFullName().equals("java.lang.Object"))
                    addedObject = true;
            }
            if (t instanceof ArrayType && !addedObject) {
                res.add(this.pmi.getServiceConfiguration().getNameInfo().getJavaLangObject());
                addedObject = true;
            }
        }
        return res;
    }

    public List<ClassType> getAllSupertypes() {
        return this.pmi.getAllSubtypes(this);
    }

    public List<? extends Field> getFields() {
        return null;
    }

    public List<Field> getAllFields() {
        return this.pmi.getAllFields(this);
    }

    public List<Method> getMethods() {
        return null;
    }

    public List<Method> getAllMethods() {
        return this.pmi.getAllMethods(this);
    }

    public List<Constructor> getConstructors() {
        return null;
    }

    public List<ClassType> getAllTypes() {
        return null;
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }

    public boolean isFinal() {
        return false;
    }

    public boolean isStatic() {
        return false;
    }

    public boolean isPrivate() {
        return false;
    }

    public boolean isProtected() {
        return false;
    }

    public boolean isPublic() {
        return false;
    }

    public boolean isStrictFp() {
        return false;
    }

    public ClassType getContainingClassType() {
        return null;
    }

    public List<? extends AnnotationUse> getAnnotations() {
        return null;
    }

    public List<? extends ClassType> getTypes() {
        return null;
    }

    public Package getPackage() {
        return null;
    }

    public ClassTypeContainer getContainer() {
        return null;
    }
}
