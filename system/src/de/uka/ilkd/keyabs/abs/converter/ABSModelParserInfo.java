package de.uka.ilkd.keyabs.abs.converter;

import java.io.File;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.ASTNode;
import abs.frontend.ast.ClassDecl;
import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.DataTypeDecl;
import abs.frontend.ast.FunctionDecl;
import abs.frontend.ast.InterfaceDecl;
import abs.frontend.ast.InterfaceTypeUse;
import abs.frontend.ast.MethodSig;
import abs.frontend.ast.Model;
import abs.frontend.ast.ParametricDataTypeDecl;
import abs.frontend.ast.TypeDecl;
import abs.frontend.ast.VarDecl;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.keyabs.abs.abstraction.ABSDatatype;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;

public class ABSModelParserInfo {

    public static final Name ABS_BOOLEAN_TYPE_NAME = new Name("ABS.StdLib.Bool");
    public static final Name ABS_INT_TYPE_NAME     = new Name("ABS.StdLib.Int");

    private static Sort checkBuiltInType(IServices iServices,
            Entry<Name, DataTypeDecl> dataType) {
        Sort dataTypeSort = null;
        if (dataType.getKey().equals(ABS_INT_TYPE_NAME)) {
            dataTypeSort = (Sort) iServices.getNamespaces().sorts()
                    .lookup(new Name("int"));
        } else if (dataType.getKey().equals(ABS_BOOLEAN_TYPE_NAME)) {
            dataTypeSort = (Sort) iServices.getNamespaces().sorts()
                    .lookup(new Name("boolean"));
        }
        return dataTypeSort;
    }

    private static String createFullyQualifiedName(InterfaceTypeUse ifdecl) {
        return ifdecl.getModuleDecl().getName() + "." + ifdecl.getName();
    }

    private static String createFullyQualifiedName(final TypeDecl interf) {
        return interf.getModule().getName() + "." + interf.getName();
    }

    private String createFullyQualifiedName(ClassDecl classDecl) {
        return classDecl.getModule().getName() + "." + classDecl.getName();
    }

    private static ImmutableSet<Sort> createListOfExtendedSortsFromTypeDeclaration(
            IServices iServices, final HashMap<Name, KeYJavaType> names2type,
            Entry<Name, InterfaceDecl> interf) {
        ImmutableSet<Sort> extSorts = DefaultImmutableSet.<Sort> nil();
        for (InterfaceTypeUse ifdecl : interf.getValue()
                .getExtendedInterfaceUseList()) {

            Name itfName = new Name(createFullyQualifiedName(ifdecl));
            Sort extSort = (Sort) iServices.getNamespaces().sorts()
                    .lookup(itfName);

            if (extSort == null) {// should actually always hold
                extSort = names2type.get(itfName).getSort();
            }
            assert extSort != null;
            extSorts = extSorts.add(extSort);
        }
        return extSorts;
    }

    private HashMap<Name, ClassDecl> classes = new HashMap<Name, ClassDecl>();
    private final HashMap<Name, InterfaceDecl> interfaces = new HashMap<Name, InterfaceDecl>();
    private final DataTypeDescriptor datatypes = new DataTypeDescriptor();
    private final DataTypeDescriptor parametricDatatypes = new DataTypeDescriptor();

    private final CoreAbsBackend absBackend;
    private String sourceDirectory;

    private String[] compilationUnitsFiles;

    private JavaModel absModelDescription;

    private boolean alreadyParsed;

    private ASTNode absModel;

    public ABSModelParserInfo() {
        this.absBackend = new CoreAbsBackend();
        this.absBackend.setWithStdLib(true);
    }

    public void finish(IServices iServices) {
        // create KeYJavaTypes and put them in map
        registerAndCreateABSInterfaceType2SortMapping(iServices);
        registerAndCreateABSDataType2SortMapping(iServices);
    }
    
    public CoreAbsBackend getABSBackend() {
    	return absBackend;
    }

    public Model parseInContext(String s) throws IOException {
    	File f = File.createTempFile("keyabs", ".abs");
    	FileWriter fw = new FileWriter(f);
    	fw.write(s);
    	fw.close();
    	List<String> files = new ArrayList();
    	files.addAll(Arrays.asList(compilationUnitsFiles));
        files.add(f.getAbsolutePath());
    	for (String cu : files) {
    		System.out.println(cu);
    	}
    	return absBackend.parseFiles(files.toArray(new String[0]));
    }
    
    public DataTypeDescriptor getDatatypes() {
        return datatypes;
    }

    public DataTypeDescriptor getParametricDatatypes() {
        return parametricDatatypes;
    }

    public HashMap<Name, InterfaceDecl> getInterfaces() {
        return interfaces;
    }

    public HashMap<Name, ClassDecl> getClasses() {
        return classes;
    }

    private void printTree(ASTNode node) {
        for (int i = 0; i < node.getNumChild(); i++) {
            printTree(node.getChild(i));
        }
    }

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

    public void setup(JavaModel absModel) {
        this.absModelDescription = absModel;
        if (absModel == JavaModel.NO_MODEL) {
            compilationUnitsFiles = new String[0];
            return;
        }
        sourceDirectory = absModel.getModelDir();
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
        List<DataConstructor> constructors = new LinkedList<DataConstructor>();
        for (DataConstructor c : decl.getDataConstructors()) {
        	constructors.add(c);
        }
        
        descr.addDataType2Constructors(dataTypeName, constructors);
    }

    private void collectTypesAndFunctionDeclarations(ASTNode<?> child) {
        try {
            for (int i = 0; i < child.getNumChild(); i++) {
                ASTNode<?> currentNode = child.getChild(i);
                if (currentNode instanceof InterfaceDecl) {
                    final InterfaceDecl interf = (InterfaceDecl) currentNode;
                    interfaces.put(new Name(createFullyQualifiedName(interf)),
                            interf);
                } else if (currentNode instanceof ParametricDataTypeDecl) {

                    final ParametricDataTypeDecl dataType = (ParametricDataTypeDecl) currentNode;
                    final Name dataTypeName = new Name(
                            createFullyQualifiedName(dataType));

                    if (dataType.getNumTypeParameter() > 0) {
                        parametricDatatypes.addDatatype(dataTypeName, dataType);
                        collectConstructors(dataType, dataTypeName,
                                parametricDatatypes);
                    } else {
                        datatypes.addDatatype(dataTypeName, dataType);
                        collectConstructors(dataType, dataTypeName, datatypes);
                    }
                } else if (currentNode instanceof ClassDecl) {
                    classes.put(new Name(
                            createFullyQualifiedName((ClassDecl) currentNode)),
                            (ClassDecl) currentNode);
                } else if (currentNode instanceof FunctionDecl) {
                    FunctionDecl fd = (FunctionDecl) currentNode;
                    /*
                     * System.out.println(fd.getName() + ":" +
                     * fd.qualifiedName() + ":::" + fd.getParamList() + ":::" +
                     * fd.getTypeUse() + ":::" +
                     * fd.getTypeUse().getDecl().isTypeParameter());
                     */
                } else if (currentNode instanceof MethodSig) {
                    MethodSig msig = (MethodSig) currentNode;
                    // System.out.println("Method" + msig.getName());
                } else if (currentNode instanceof VarDecl) {
                    VarDecl vd = (VarDecl) currentNode;
                    /*
                     * System.out.println("Local Var " + vd.getName() + " " +
                     * vd.getType() + " " + vd.getInitExp());
                     */
                } else {
                    collectTypesAndFunctionDeclarations(currentNode);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void registerAndCreateABSDataType2SortMapping(IServices iServices) {
        Sort topSort = Sort.ANY;

        assert topSort != null;

        for (Entry<Name, DataTypeDecl> dataType : datatypes.getDatatypes()
                .entrySet()) {
            final ABSDatatype absType = new ABSDatatype(dataType.getKey());
            Sort dataTypeSort = (Sort) iServices.getNamespaces().sorts()
                    .lookup(dataType.getKey());
            if (dataTypeSort == null) {
                dataTypeSort = checkBuiltInType(iServices, dataType);
                if (dataTypeSort == null) {
                    dataTypeSort = new SortImpl(dataType.getKey(), topSort);
                }
            }
            final KeYJavaType abs2sort = new KeYJavaType(absType, dataTypeSort);
            iServices.getProgramInfo().rec2key().put(absType, abs2sort);
        }
    }
    
    
    private void registerAndCreateABSInterfaceType2SortMapping(
            IServices iServices) {
        Sort anyInterfaceSort = (Sort) iServices.getNamespaces().sorts()
                .lookup(new ProgramElementName("ABSAnyInterface"));

        assert anyInterfaceSort != null;

        Entry<Name, InterfaceDecl>[] interfArray = sortInterfacesAscendingInNumberOfExtendedTypes();

        final HashMap<Name, KeYJavaType> names2type = new HashMap<Name, KeYJavaType>();

        for (Entry<Name, InterfaceDecl> interf : interfArray) {
            final ABSInterfaceType absType = new ABSInterfaceType(
                    interf.getKey());
            Sort interfaceSort = (Sort) iServices.getNamespaces().sorts()
                    .lookup(interf.getKey());

            if (interfaceSort == null) {
                if (interf.getValue().getExtendedInterfaceUseList()
                        .getNumChild() == 0) {
                    interfaceSort = new SortImpl(interf.getKey(),
                            anyInterfaceSort);
                } else {
                    ImmutableSet<Sort> extSorts = createListOfExtendedSortsFromTypeDeclaration(
                            iServices, names2type, interf);
                    interfaceSort = new SortImpl(interf.getKey(), extSorts,
                            true);
                }
            }

            final KeYJavaType abs2sort = new KeYJavaType(absType, interfaceSort);
            iServices.getProgramInfo().rec2key().put(absType, abs2sort);
        }
    }
    
    
    

    private Entry<Name, InterfaceDecl>[] sortInterfacesAscendingInNumberOfExtendedTypes() {
        @SuppressWarnings("unchecked")
        Entry<Name, InterfaceDecl>[] interfArray = interfaces.entrySet()
                .toArray(new Entry[interfaces.size()]);

        Arrays.sort(interfArray, new Comparator<Entry<Name, InterfaceDecl>>() {
            @Override
            public int compare(Entry<Name, InterfaceDecl> o1,
                    Entry<Name, InterfaceDecl> o2) {
                int extendedTypes1 = o1.getValue()
                        .getExtendedInterfaceUseList().getNumChild();
                int extendedTypes2 = o2.getValue()
                        .getExtendedInterfaceUseList().getNumChild();
                return extendedTypes1 < extendedTypes2 ? 1
                        : extendedTypes1 > extendedTypes2 ? -1 : 0;
            }
        });
        return interfArray;
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
