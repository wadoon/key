package de.uka.ilkd.keyabs.abs.converter;

import abs.frontend.ast.ClassDecl;
import abs.frontend.ast.FieldDecl;
import de.uka.ilkd.key.logic.Name;

import java.util.ArrayList;
import java.util.List;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 09.03.13
 * Time: 11:42
 * To change this template use File | Settings | File Templates.
 */
public class ClassDescriptor {

    private final Name className;
    private final List<FieldDecl> fields;
    private final ClassDecl classDeclaration;

    public ClassDescriptor(String fullyQualifiedName, ClassDecl cd) {
        this.className = new Name(fullyQualifiedName);
        this.classDeclaration = cd;
        this.fields = new ArrayList<>();
    }

    public Name name() {
        return className;
    }

    public void addFields(FieldDecl fd) {
        fields.add(fd);
    }

    public List<FieldDecl> getFields() {
        return fields;
    }

    public String toString() {
        return "class" + className + " has fields " + fields;
    }

}
