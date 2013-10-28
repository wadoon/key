package de.uka.ilkd.keyabs.proof.init;

import abs.frontend.ast.*;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.keyabs.abs.ABSInfo;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.abstraction.ABSDatatype;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.abs.converter.ABSModelParserInfo;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

public class SortBuilder {

    // type names of the integer and boolean type in ABS
    public static final Name ABS_ANY_INTERFACE_SORT_NAME = new Name("ABSAnyInterface");
    public static final Name ABS_BOOLEAN_TYPE_NAME = new Name("ABS.StdLib.Bool");
    public static final Name ABS_INT_TYPE_NAME = new Name("ABS.StdLib.Int");
    public static final Name ABS_FUTURE_TYPE_NAME = new Name("ABS.StdLib.Fut");

    private static Sort checkBuiltInType(ABSServices services,
                                         Name dataType) {
        Sort dataTypeSort = null;
        if (dataType.equals(ABS_INT_TYPE_NAME)) {
            dataTypeSort = services.getTypeConverter().getIntegerLDT()
                    .targetSort();
        } else if (dataType.equals(ABS_BOOLEAN_TYPE_NAME)) {
            dataTypeSort = services.getTypeConverter().getBooleanLDT()
                    .targetSort();
        } else if (dataType.equals(ABS_FUTURE_TYPE_NAME)) {
            dataTypeSort = services.getTypeConverter().getHistoryLDT()
                    .getFutureSort();
        }
        return dataTypeSort;
    }

    public static String createFullyQualifiedName(final Decl interf) {
        return interf.moduleName() + "." + interf.getName();
    }

    public static String createFullyQualifiedName(final TypeUse interf) {
        return interf.getModuleDecl().getName() + "." + interf.getName();
    }

    private ImmutableSet<Sort> createListOfExtendedSortsFromTypeDeclaration(
            ABSInitConfig initConfig,
            ABSServices services,
            final HashMap<Name, KeYJavaType> names2type,
            Sort anyInterfaceSort,
            InterfaceDecl itf) {
        ImmutableSet<Sort> extSorts = DefaultImmutableSet.<Sort>nil();
        for (InterfaceTypeUse ifdecl : itf.getExtendedInterfaceUseList()) {

            Name itfName = new Name(createFullyQualifiedName(ifdecl));
            Sort extSort = services.getNamespaces().sorts().lookup(itfName);

            if (extSort == null) {// should actually always hold
                if (names2type.containsKey(itfName)) {
                    extSort = names2type.get(itfName).getSort();
                } else {
                    extSort = registerInterfaceType(initConfig, services,
                            names2type, anyInterfaceSort, itfName, (InterfaceDecl) ifdecl.getDecl());
                }
            }
            assert extSort != null;
            extSorts = extSorts.add(extSort);
        }
        return extSorts;
    }

    public void createAndRegisterSorts(ABSInitConfig initConfig) {

        final ABSInfo info = initConfig.getServices().getProgramInfo();
        final ABSModelParserInfo absModelInfo = info.getABSParserInfo();
        final ABSServices services = initConfig.getServices();

        // get super sort of all interface sorts
        final Namespace<Sort> sorts = services.getNamespaces().sorts();
        final Sort anyInterfaceSort = sorts.lookup(ABS_ANY_INTERFACE_SORT_NAME);
        assert anyInterfaceSort != null;

        Sort topSort = Sort.ANY;

        assert topSort != null;

        initializeDatatypeSorts(info, services, topSort);
        initializeInterfaceSorts(initConfig, absModelInfo, services, anyInterfaceSort);
        initializeGenericDatatypes(initConfig, info, services, topSort);
    }

    private void initializeGenericDatatypes(ABSInitConfig initConfig, ABSInfo info, ABSServices services, Sort topSort) {
        System.out.println("Instantiating Generic Datatypes");
        for (DataTypeDecl d : info.getABSParserInfo().getParametricDatatypes()
                .getDatatypes().values()) {

            // create base data type first
            final Name baseName = new Name(createFullyQualifiedName(d));
            final ABSDatatype type = new ABSDatatype(baseName);
            Sort dataTypeSort = initConfig.sortNS().lookup(baseName);
            if (dataTypeSort == null) {
                dataTypeSort = checkBuiltInType(services, baseName);
                if (dataTypeSort == null) {
                    dataTypeSort = new SortImpl(baseName, topSort);
                    initConfig.sortNS().addSafely(dataTypeSort);
                }
                final KeYJavaType abs2sort = new KeYJavaType(type, dataTypeSort);
                services.getProgramInfo().rec2key().put(type, abs2sort);
            }


            /* for (DataConstructor cons : d.getDataConstructorList()) {
                System.out.println("DATACONS:" + cons.getType().getQualifiedName());
                System.out.println(cons.getName() + ":" + cons.getType());
            }*/

            // create instantiated data type
            /*
             * for (KeYJavaType s : initConfig.getServices().getProgramInfo().getAllKeYJavaTypes()) {
             * final Name name = new Name(baseName + "<" + s.getFullName() +
             * ">"); type = new ABSDatatype(name); dtSort = new SortImpl(name);
             * initConfig.sortNS().addSafely(dtSort); abs2sort = new
             * KeYJavaType(type, dtSort);
             * services.getProgramInfo().rec2key().put(type, abs2sort); }
             */
        }
    }

    private void initializeInterfaceSorts(ABSInitConfig initConfig, ABSModelParserInfo absModelInfo,
                                          ABSServices services, Sort anyInterfaceSort) {
        // create and register sorts and KeYJavaTypes
        final Entry<Name, InterfaceDecl>[] interfaces =
                sortInterfacesAscendingInNumberOfExtendedTypes(absModelInfo
                        .getInterfaces());

        final HashMap<Name, KeYJavaType> names2type = new HashMap<Name, KeYJavaType>();
        for (Entry<Name, InterfaceDecl> itf : interfaces) {
            registerInterfaceType(initConfig, services, names2type, anyInterfaceSort, itf.getKey(), itf.getValue());
        }
    }

    private Sort registerInterfaceType(ABSInitConfig initConfig,
                                       ABSServices services,
                                       HashMap<Name, KeYJavaType> names2type,
                                       Sort anyInterfaceSort,
                                       Name itfName, InterfaceDecl itf) {
        Sort interfaceSort = initConfig.sortNS().lookup(itfName);
        final ABSInterfaceType absType = new ABSInterfaceType(itfName);

        if (interfaceSort == null) {
            if (itf.getExtendedInterfaceUseList().getNumChild() == 0) {
                interfaceSort = new SortImpl(itfName, anyInterfaceSort);
            } else {
                final ImmutableSet<Sort> extSorts = createListOfExtendedSortsFromTypeDeclaration(
                        initConfig, services, names2type, anyInterfaceSort, itf);
                interfaceSort = new SortImpl(itfName, extSorts, true);
            }
            initConfig.sortNS().addSafely(interfaceSort);
        }

        final KeYJavaType abs2sort = new KeYJavaType(absType, interfaceSort);
        services.getProgramInfo().rec2key().put(absType, abs2sort);
        return interfaceSort;
    }

    private void initializeDatatypeSorts(ABSInfo info, ABSServices services, Sort topSort) {
        for (Entry<Name, DataTypeDecl> dataType : info.getABSParserInfo()
                .getDatatypes().getDatatypes().entrySet()) {
            final ABSDatatype absType = new ABSDatatype(dataType.getKey());
            Sort dataTypeSort = checkBuiltInType(services, dataType.getKey());
            if (dataTypeSort == null) {
                dataTypeSort = services.getNamespaces().sorts().lookup(dataType.getKey());
                if (dataTypeSort == null) {
                    dataTypeSort = new SortImpl(dataType.getKey(), topSort);
                }
            }
            final KeYJavaType abs2sort = new KeYJavaType(absType, dataTypeSort);
            services.getProgramInfo().rec2key().put(absType, abs2sort);
        }
    }

    private Entry<Name, InterfaceDecl>[] sortInterfacesAscendingInNumberOfExtendedTypes(
            Map<Name, InterfaceDecl> interfaces) {
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

}
