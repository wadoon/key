package de.uka.ilkd.keyabs.proof.init;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import abs.frontend.analyser.SemanticErrorList;
import abs.frontend.analyser.TypeError;
import abs.frontend.ast.*;
import abs.frontend.typechecker.Type;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.keyabs.abs.ABSInfo;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.converter.ClassDescriptor;
import de.uka.ilkd.keyabs.logic.ldt.HeapLDT;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public class FunctionBuilder {


    private Sort getType(Type t, ABSInfo info) {
        if (t.isTypeParameter()) {
            return Sort.ANY;
        } else {        	
            return info.getTypeByName(t.getQualifiedName()).getSort();
        }
    }

    public void createAndRegisterABSFunctions(ABSInitConfig initConfig) {

        final ABSServices services  = initConfig.getServices();
        final ABSInfo     info      = services.getProgramInfo();
        final HistoryLDT historyLDT = services.getTypeConverter().getHistoryLDT();
        final HeapLDT heapLDT       = services.getTypeConverter().getHeapLDT();

        final Namespace<SortedOperator> funcNS = initConfig.getServices().getNamespaces().functions();
        final Namespace<IProgramVariable> progVarNS = initConfig.getServices().getNamespaces().programVariables();

        Collection<List<DataConstructor>> dataType2ConstructorMap = info
                .getABSParserInfo().getDatatypes()
                .getDataTypes2dataConstructors().values();

        createConstructorFunctions(info, funcNS, dataType2ConstructorMap);

        createConstructorFunctions(info, funcNS, info.getABSParserInfo()
                .getParametricDatatypes().getDataTypes2dataConstructors()
                .values());


        System.out.println("Register Global Functions");
        for (Map.Entry<Name, FunctionDecl> func : info.getABSParserInfo().getFunctions().entrySet()) {
            final FunctionDecl absFuncDecl = func.getValue();
	    final Sort[] argSorts = new Sort[absFuncDecl.getNumParam()];
            int count = 0;
            for (ParamDecl arg : absFuncDecl.getParamList()) {
                argSorts[count++] = getType(arg.getType(), info);
            }

            Function function = new Function(func.getKey(),
                    getType(absFuncDecl.getType(), info),
                    argSorts, null, false);

          
            funcNS.add(function);
        }


        System.out.println("Register Interface Label Constants and Invariant Symbols");

        for (Name itf : info.getABSParserInfo().getInterfaces().keySet()) {
            Function interfaceLabel = new Function(itf,
                    services.getTypeConverter().getHistoryLDT()
                            .getInterfaceLabelSort(), new Sort[0], null, true);
            funcNS.add(interfaceLabel);

            Function iinv = new Function(new Name(itf.toString() + "$IInv"),
                    Sort.FORMULA, new Sort[]{services.getTypeConverter().getHistoryLDT().targetSort()}, null, false);
            funcNS.add(iinv);
        }

        System.out.println("Register Class Label Constants");

        for (Name className : info.getABSParserInfo().getClasses().keySet()) {
            Function classLabel = new Function(className,
                    historyLDT.getClassLabelSort(), new Sort[0], null, true);
            funcNS.add(classLabel);

        }

        System.out.println("Register Method Label Constants");
        for (InterfaceDecl itfDecl : info.getABSParserInfo().getInterfaces().values()) {
            for (MethodSig  msig : itfDecl.getBodys()) {
                Name methodName = createNameFor(msig, itfDecl);
                Function methodLabel = new Function(methodName,
                        historyLDT.getMethodLabelSort(), new Sort[0], null, true);
                funcNS.add(methodLabel);
            }
        }

        System.out.println("Register Fields ");
        for (ClassDescriptor classDescriptor : info.getABSParserInfo().getClasses().values()) {
            for (FieldDecl  field : classDescriptor.getFields()) {
                registerField(services, heapLDT, funcNS, progVarNS, classDescriptor, field);

            }
            for (ParamDecl field : classDescriptor.getParams()) {
                registerField(services, heapLDT, funcNS, progVarNS, classDescriptor, field);
            }
        }


        // Register ABS functions

        System.out.println("Register future getters");

        GenericSort depSort = new GenericSort(new Name("T"));
        SortDependingFunction futGetterProto = SortDependingFunction
                .createFirstInstance(depSort, new Name("get"), depSort,
                        new Sort[] { historyLDT.targetSort() }, false);

        for (KeYJavaType t : info.getAllKeYJavaTypes()) {
            if (t.getSort().extendsTrans(historyLDT.getFutureSort())) {
                futGetterProto.getInstanceFor(t.getSort(),
                        initConfig.getServices());
            }
        }

    }

    private void registerField(ABSServices services, HeapLDT heapLDT,
                               Namespace<SortedOperator> funcNS, Namespace<IProgramVariable> progVarNS,
                               ClassDescriptor classDescriptor, TypedVarOrFieldDecl field) {
        final ProgramElementName fieldName = new ProgramElementName(field.getName(),
                classDescriptor.name().toString());
        final Function fieldFct = new Function(fieldName,
                heapLDT.getFieldSort(), new Sort[0], null, true);
        progVarNS.add(new LocationVariable(fieldName,
                services.getJavaInfo().getKeYJavaType(field.getType().getQualifiedName()),
                new KeYJavaType(),
                false, false));
        funcNS.add(fieldFct);
    }

    public static Name createNameFor(FunctionDecl fd) {
        return new ProgramElementName(fd.getName(), fd.moduleName());
    }


    public static Name createNameFor(MethodSig msig, InterfaceDecl itfDecl) {
        String base = msig.getName();

        for (ParamDecl p : msig.getParamList()) {
            base += "#" + p.getType().getQualifiedName();
        }
        return new ProgramElementName(base, itfDecl.qualifiedName());
    }

    private void createConstructorFunctions(final ABSInfo info,
                                            final Namespace<SortedOperator> funcNS,
                                            Collection<List<DataConstructor>> dataType2ConstructorMap) {
        for (final List<DataConstructor> constructors : dataType2ConstructorMap) {
            for (DataConstructor c : constructors) {
                final Sort[] argSorts = new Sort[c.getConstructorArgList()
                        .getNumChild()];

                try {
                    int count = 0;
                    for (ConstructorArg arg : c.getConstructorArgs()) {
                        if (arg.getType().isTypeParameter()) {
                            argSorts[count++] = Sort.ANY;
                        } else {
                            argSorts[count++] = info.getTypeByName(
                                    arg.getType().getQualifiedName()).getSort();
                        }
                    }
                    if (count == argSorts.length) {
                        // create unique function symbol
                        final String fullyQualifiedName = c.moduleName()
                                + "."
                                + c.getDataTypeDecl().getName();

                        final ProgramElementName funcName = new ProgramElementName(c.getName(),
                                fullyQualifiedName);

                        if (funcNS.lookup(funcName) == null) {
                            Sort returnSort = info.getTypeByName(
                                    c.getType().getQualifiedName()).getSort();
                            Function constructorFct = new Function(
                                    new ProgramElementName(c.getName(),
                                            fullyQualifiedName), returnSort,
                                    argSorts, null, true);

                            funcNS.add(constructorFct);
                        }
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
    }

}
