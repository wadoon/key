package de.uka.ilkd.keyabs.gui;

import abs.frontend.ast.MethodImpl;
import abs.frontend.ast.ParamDecl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.keyabs.abs.ABSServices;

import java.util.*;

public class POBrowserData {
    private Name[] classes;
    private final ABSServices services;

    public POBrowserData(ABSServices services) {
        this.services = services;
        Set<Name> classes = services.getProgramInfo().getABSParserInfo().getClasses().keySet();
        this.classes = classes.toArray(new Name[classes.size()]);
        Arrays.sort(this.classes);
    }

    public Name[] getClasses() {
        return classes;
    }

    public MethodRepresentative[] getMethods(Name selectedClass) {
        List<MethodRepresentative> methods = new LinkedList<>();
        for (MethodImpl m : services.getProgramInfo().getAllMethods(selectedClass)) {
            methods.add(new MethodRepresentative(m));
        }
        return methods.toArray(new MethodRepresentative[methods.size()]);
    }



    public class MethodRepresentative {
        private MethodImpl method;

        public  MethodRepresentative(MethodImpl method) {
            this.method = method;
        }


        public String toString() {
           String name = method.getMethodSig().getName();
           name += "(";
           boolean afterFirst = false;
           for (ParamDecl p : method.getMethodSig().getParamList()) {
               if (afterFirst) {
                   name+=", ";
               } else {
                   afterFirst = true;
               }
               name += p.getType().getSimpleName();
           }
          return name + ")";

        }

    }
}