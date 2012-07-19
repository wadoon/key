package de.uka.ilkd.keyabs.abs.converter;

import java.io.File;
import java.util.HashMap;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.ASTNode;
import abs.frontend.ast.CompilationUnit;
import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.DataTypeDecl;
import abs.frontend.ast.InterfaceDecl;
import abs.frontend.ast.List;
import de.uka.ilkd.key.logic.ProgramElementName;

public class ABSInterfaceCollector {

    private final HashMap<ProgramElementName, InterfaceDecl> interfaces = new HashMap<ProgramElementName, InterfaceDecl>();
    private final HashMap<ProgramElementName, DataTypeDecl> datatypes = new HashMap<ProgramElementName, DataTypeDecl>();
    private final HashMap<ProgramElementName, List<DataConstructor>> dataTypes2dataConstructors = new HashMap<ProgramElementName, List<DataConstructor>>();
    
    
    
    public HashMap<ProgramElementName, InterfaceDecl> getInterfaces() {
        return interfaces;
    }

    public HashMap<ProgramElementName, DataTypeDecl> getDatatypes() {
        return datatypes;
    }

    public HashMap<ProgramElementName, List<DataConstructor>> getDataTypes2dataConstructors() {
        return dataTypes2dataConstructors;
    }

    public ABSInterfaceCollector() {
        
    }
    
    public void collect() {
        CoreAbsBackend core = new CoreAbsBackend();
        try {
            CompilationUnit model = core.parseUnit(new File("/Users/bubel/tmp/testabs/pong.abs"));

            collect(model);

        } catch (Exception e) {
            e.printStackTrace();
        }
    }    

    private void collect(ASTNode child) {
        try {
            for (int i = 0; i<child.getNumChild(); i++) {
                if (child.getChild(i) instanceof InterfaceDecl) {
                    
                    InterfaceDecl interf = (InterfaceDecl) child.getChild(i);                  
                    interfaces.put(new ProgramElementName(interf.getName(), interf.getModule().getName()), interf);
                    
                    System.out.println("Found interface: "+interf.getName() + ":" +interf.getModule().getName());
                } else if (child.getChild(i) instanceof DataTypeDecl) {                    
                    DataTypeDecl dataType = (DataTypeDecl) child.getChild(i);
                    final ProgramElementName dataTypeName = new ProgramElementName(dataType.getName(), dataType.getModule().getName());
                    datatypes.put(dataTypeName, dataType);

                    collectConstructors(dataType, dataTypeName);                    
                    System.out.println("Found datatype: "+dataType.getName() + ":" +dataType.getModule().getName());
                } else {
                    collect(child.getChild(i));
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }    

    
    private void collectConstructors(DataTypeDecl decl, ProgramElementName dataTypeName) {
        List<DataConstructor> constructors = decl.getDataConstructors();
        dataTypes2dataConstructors.put(dataTypeName, constructors);
        
    }
    
    
}
