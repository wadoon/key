package de.uka.ilkd.keyabs.init;

import java.util.*;
import java.util.Map.Entry;

import abs.frontend.ast.*;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.IServices;
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

public class SortBuilder {

    // type names of the integer and boolean type in ABS
    public static final Name ABS_BOOLEAN_TYPE_NAME = new Name("ABS.StdLib.Bool");
    public static final Name ABS_INT_TYPE_NAME = new Name("ABS.StdLib.Int");

    private static Sort checkBuiltInType(IServices services,
            Entry<Name, DataTypeDecl> dataType) {
        Sort dataTypeSort = null;
        if (dataType.getKey().equals(ABS_INT_TYPE_NAME)) {
            dataTypeSort = services.getTypeConverter().getIntegerLDT()
                    .targetSort();
        } else if (dataType.getKey().equals(ABS_BOOLEAN_TYPE_NAME)) {
            dataTypeSort = services.getTypeConverter().getBooleanLDT()
                    .targetSort();
        }
        return dataTypeSort;
    }

    public static String createFullyQualifiedName(final TypeDecl interf) {
        return interf.getModule().getName() + "." + interf.getName();
    }

    public static String createFullyQualifiedName(final TypeUse interf) {
        return interf.getModuleDecl().getName() + "." + interf.getName();
    }

    private static ImmutableSet<Sort> createListOfExtendedSortsFromTypeDeclaration(
            IServices iServices, final HashMap<Name, KeYJavaType> names2type,
            Entry<Name, InterfaceDecl> interf) {
        ImmutableSet<Sort> extSorts = DefaultImmutableSet.<Sort> nil();
        for (InterfaceTypeUse ifdecl : interf.getValue()
                .getExtendedInterfaceUseList()) {

            Name itfName = new Name(createFullyQualifiedName(ifdecl));
            Sort extSort = iServices.getNamespaces().sorts().lookup(itfName);

            if (extSort == null) {// should actually always hold
                extSort = names2type.get(itfName).getSort();
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
        final Sort anyInterfaceSort = sorts.lookup(new Name("ABSAnyInterface"));
        assert anyInterfaceSort != null;

        Sort topSort = Sort.ANY;

        assert topSort != null;

        for (Entry<Name, DataTypeDecl> dataType : info.getABSParserInfo()
                .getDatatypes().getDatatypes().entrySet()) {
            final ABSDatatype absType = new ABSDatatype(dataType.getKey());
            Sort dataTypeSort = sorts.lookup(dataType.getKey());
            if (dataTypeSort == null) {
                dataTypeSort = checkBuiltInType(services, dataType);
                if (dataTypeSort == null) {
                    dataTypeSort = new SortImpl(dataType.getKey(), topSort);
                }
            }
            final KeYJavaType abs2sort = new KeYJavaType(absType, dataTypeSort);
            services.getProgramInfo().rec2key().put(absType, abs2sort);
        }

        // create and register sorts and KeYJavaTypes
        final Entry<Name, InterfaceDecl>[] interfaces = sortInterfacesAscendingInNumberOfExtendedTypes(absModelInfo
                .getInterfaces());

        final HashMap<Name, KeYJavaType> names2type = new HashMap<Name, KeYJavaType>();
        for (Entry<Name, InterfaceDecl> itf : interfaces) {
            final ABSInterfaceType absType = new ABSInterfaceType(itf.getKey());
            Sort interfaceSort = sorts.lookup(itf.getKey());

            if (interfaceSort == null) {
                if (itf.getValue().getExtendedInterfaceUseList().getNumChild() == 0) {
                    interfaceSort = new SortImpl(itf.getKey(), anyInterfaceSort);
                } else {
                    ImmutableSet<Sort> extSorts = createListOfExtendedSortsFromTypeDeclaration(
                            services, names2type, itf);
                    interfaceSort = new SortImpl(itf.getKey(), extSorts, true);
                }
                initConfig.sortNS().addSafely(interfaceSort);
            }

            final KeYJavaType abs2sort = new KeYJavaType(absType, interfaceSort);
            services.getProgramInfo().rec2key().put(absType, abs2sort);
        }

        System.out.println("Instantiating Generic Datatypes");
        for (DataTypeDecl d : info.getABSParserInfo().getParametricDatatypes()
                .getDatatypes().values()) {

            // create base data type first
            Name baseName = new Name(createFullyQualifiedName(d));
            ABSDatatype type = new ABSDatatype(baseName);
            Sort dtSort = new SortImpl(baseName);
            initConfig.sortNS().addSafely(dtSort);
            KeYJavaType abs2sort = new KeYJavaType(type, dtSort);
            services.getProgramInfo().rec2key().put(type, abs2sort);

            // create instantiated datatype
            /*
             * for (KeYJavaType s :
             * initConfig.getServices().getProgramInfo().getAllKeYJavaTypes()) {
             * final Name name = new Name(baseName + "<" + s.getFullName() +
             * ">"); type = new ABSDatatype(name); dtSort = new SortImpl(name);
             * initConfig.sortNS().addSafely(dtSort); abs2sort = new
             * KeYJavaType(type, dtSort);
             * services.getProgramInfo().rec2key().put(type, abs2sort); }
             */
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
