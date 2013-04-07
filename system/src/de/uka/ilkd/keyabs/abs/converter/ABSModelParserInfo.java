package de.uka.ilkd.keyabs.abs.converter;

import java.io.File;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.*;
import java.util.List;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.keyabs.proof.init.FunctionBuilder;
import de.uka.ilkd.keyabs.proof.init.SortBuilder;

/**
 * This class reads in the ABS model and collects the necessary information about the model like
 * existing datatypes, interfaces, classes and methods.
 * 
 * The information is later used to create the necessary logic elements. 
 * 
 * @author Richard Bubel
 *
 */
public class ABSModelParserInfo {

    private HashMap<Name, ClassDescriptor> classes = new HashMap<Name, ClassDescriptor>();
    private final HashMap<Name, InterfaceDecl> interfaces = new HashMap<Name, InterfaceDecl>();
    private final HashMap<Name, FunctionDecl> functions = new HashMap<>();
    private final DataTypeDescriptor datatypes = new DataTypeDescriptor();
    private final DataTypeDescriptor parametricDatatypes = new DataTypeDescriptor();

    private final CoreAbsBackend absBackend;
    private String sourceDirectory;

    private String[] compilationUnitsFiles;

    private JavaModel absModelDescription;

    private boolean alreadyParsed;

    private ASTNode<?> absModel;

    public ABSModelParserInfo() {
        this.absBackend = new CoreAbsBackend();
        this.absBackend.setWithStdLib(true);
    }

    public CoreAbsBackend getABSBackend() {
    	return absBackend;
    }

    /**
     * parses the given String in the context of this model
     * @param s the String to parse
     * @return the parsed model
     * @throws IOException if an IO error occurs
     */
    public Model parseInContext(String s) throws IOException {
    	//create a temporary file and store write the string to parse to this location
    	final File f = File.createTempFile("keyabs", ".abs");
    	final FileWriter fw = new FileWriter(f);
    	fw.write(s);
    	fw.close();
    	
    	// collect all file sto parse
    	final List<String> files = new ArrayList<String>();
    	files.addAll(Arrays.asList(compilationUnitsFiles));
        files.add(f.getAbsolutePath());
    	return absBackend.parseFiles(files.toArray(new String[0]));
    }

    
    /**
     * returns all non-generic datatypes present in the ABS model
     * @return all non-generic datatypes
     */
    public DataTypeDescriptor getDatatypes() {
        return datatypes;
    }

    /**
     * returns all generic datatypes present in the ABS model
     * @return all generic datatypes
     */
    public DataTypeDescriptor getParametricDatatypes() {
        return parametricDatatypes;
    }

    /**
     * returns all interfaces of the ABS model
     * @return all interfaces
     */
    public HashMap<Name, InterfaceDecl> getInterfaces() {
        return interfaces;
    }

    /**
     * returns all classes of the ABS model
     * @return all classes
     */
    public HashMap<Name, ClassDescriptor> getClasses() {
        return classes;
    }

    /**
     * read tge ABS model 
     * @throws IOException
     */
    public void readABSModel() throws IOException {
        if (!alreadyParsed && compilationUnitsFiles != null) {
            if (absModelDescription != JavaModel.NO_MODEL) {
                absModel = absBackend.parseFiles(compilationUnitsFiles);
            } else {
                absModel = absBackend.getStdLib();
            }

            collectTypesAndFunctionDeclarations(absModel);
            alreadyParsed = true;
        }
    }

    /** 
     * sets up the model with the necessary source paths
     * @param absModel contains all information about the locations of the source to be read
     */
    public void setup(JavaModel absModel) {
        this.absModelDescription = absModel;
        if (absModel == JavaModel.NO_MODEL) {
            compilationUnitsFiles = new String[0];
            return;
        }
        sourceDirectory = absModel.getModelDir();
        
        // get all abs file in the directories
        File sourceDir = new File(sourceDirectory);
        File[] compilationUnits = sourceDir.listFiles(new FilenameFilter() {
            @Override
            public boolean accept(File dir, String name) {
                return name.endsWith(".abs");
            }
        });
      
        compilationUnitsFiles = new String[compilationUnits.length];
        int i = 0;
        for (File f : compilationUnits) {
            compilationUnitsFiles[i++] = f.getAbsolutePath();
        }
    }

    private void collectConstructors(DataTypeDecl decl, Name dataTypeName,
            DataTypeDescriptor descr) {
        final List<DataConstructor> constructors = new LinkedList<DataConstructor>();
        for (final DataConstructor c : decl.getDataConstructors()) {
        	constructors.add(c);
        }
        
        descr.addDataType2Constructors(dataTypeName, constructors);
    }


    private void collectClassMembers(ClassDecl cd) {
        ClassDescriptor classDescription =
                new ClassDescriptor(SortBuilder.createFullyQualifiedName(cd), cd);

        for (FieldDecl fd : cd.getFields()) {
            classDescription.addFields(fd);
        }

        for (ParamDecl pd : cd.getParams()) {
            classDescription.addParam(pd);
        }

        for (MethodImpl md : cd.getMethodList()) {
            classDescription.addMethod(md);
        }

        classes.put(classDescription.name(), classDescription);
        collectTypesAndFunctionDeclarations(cd);
    }


    private void collectTypesAndFunctionDeclarations(ASTNode<?> child) {
        try {
            for (int i = 0; i < child.getNumChild(); i++) {
                ASTNode<?> currentNode = child.getChild(i);
                if (currentNode instanceof InterfaceDecl) {
                    final InterfaceDecl interf = (InterfaceDecl) currentNode;
                    interfaces.put(new Name(SortBuilder.createFullyQualifiedName(interf)), interf);
                    collectTypesAndFunctionDeclarations(currentNode);
                } else if (currentNode instanceof ParametricDataTypeDecl) {
                    final ParametricDataTypeDecl dataType = (ParametricDataTypeDecl) currentNode;
                    final Name dataTypeName = new Name(SortBuilder.createFullyQualifiedName(dataType));

                    if (dataType.getNumTypeParameter() > 0) {
                        parametricDatatypes.addDatatype(dataTypeName, dataType);
                        collectConstructors(dataType, dataTypeName,
                                parametricDatatypes);
                    } else {
                        datatypes.addDatatype(dataTypeName, dataType);
                        collectConstructors(dataType, dataTypeName, datatypes);
                    }
                } else if (currentNode instanceof ClassDecl) {
                    collectClassMembers((ClassDecl) currentNode);
                } else if (currentNode instanceof FunctionDecl) {
                    FunctionDecl fd = (FunctionDecl) currentNode;
                    functions.put(FunctionBuilder.createNameFor(fd), fd);
                    collectTypesAndFunctionDeclarations(currentNode);
                } else if (currentNode instanceof MethodSig) {
                    MethodSig msig = (MethodSig) currentNode;
                    addMethodSignature(msig);
                    collectTypesAndFunctionDeclarations(currentNode);
                } else if (currentNode instanceof VarDecl) {
                    VarDecl vd = (VarDecl) currentNode;
                    collectTypesAndFunctionDeclarations(currentNode);
                    /*
                     * System.out.println("Local Var " + vd.getName() + " " +
                     * vd.getType() + " " + vd.getInitExp());
                     */
                } else if (currentNode instanceof MethodImpl) {
                    MethodImpl mImpl = (MethodImpl)currentNode;
                    collectTypesAndFunctionDeclarations(currentNode);
                } else {
                    if (currentNode instanceof ParametricDataTypeUse) {
/*                        System.out.println(((TypeUse)currentNode).getDecl().qualifiedName() + "::" +
                                ((ParametricDataTypeUse)currentNode).getParamList());*/
                    }
                    collectTypesAndFunctionDeclarations(currentNode);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void addMethodSignature(MethodSig msig) {
        // TODO Auto-generated method stub
    }

    public HashMap<Name, FunctionDecl> getFunctions() {
        return functions;
    }


    public class DataTypeDescriptor {

        private HashMap<Name, DataTypeDecl> datatypes = new HashMap<Name, DataTypeDecl>();
        private HashMap<Name, List<DataConstructor>> dataTypes2dataConstructors = new HashMap<Name, List<DataConstructor>>();

        public HashMap<Name, DataTypeDecl> getDatatypes() {
            return datatypes;
        }

        public void addDatatype(Name name, DataTypeDecl dataDecl) {
            datatypes.put(name, dataDecl);
        }

        public HashMap<Name, List<DataConstructor>> getDataTypes2dataConstructors() {
            return dataTypes2dataConstructors;
        }

        public void addDataType2Constructors(Name name,
                List<DataConstructor> constructors) {
            this.dataTypes2dataConstructors.put(name, constructors);
        }
    }

}
