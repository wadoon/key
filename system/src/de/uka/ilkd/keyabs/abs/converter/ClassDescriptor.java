package de.uka.ilkd.keyabs.abs.converter;

import abs.frontend.ast.*;
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
    private final List<MethodImpl> methods;
    private final ClassDecl classDeclaration;
    private final List<ParamDecl> params;

    public ClassDescriptor(String fullyQualifiedName, ClassDecl cd) {
        this.className = new Name(fullyQualifiedName);
        this.classDeclaration = cd;
        this.fields  = new ArrayList<>();
        this.params  = new ArrayList<>();
        this.methods = new ArrayList<>();
    }

    public Name name() {
        return className;
    }

    public void addMethod(MethodImpl m) {
        methods.add(m);
    }

    public List<MethodImpl> getMethods() {
        return methods;
    }

    public void addFields(FieldDecl fd) {
        fields.add(fd);
    }

    public void addParam(ParamDecl pd) {
        params.add(pd);
    }

    public List<FieldDecl> getFields() {
        return fields;
    }

    public List<ParamDecl> getParams() {
        return params;
    }

    public String toString() {
        return "class" + className + " has fields " + fields;
    }

}
