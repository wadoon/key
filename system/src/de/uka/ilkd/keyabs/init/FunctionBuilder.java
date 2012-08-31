package de.uka.ilkd.keyabs.init;

import java.util.Collection;
import java.util.List;

import abs.frontend.ast.ConstructorArg;
import abs.frontend.ast.DataConstructor;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.keyabs.abs.ABSInfo;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public class FunctionBuilder {

    public void createAndRegisterABSFunctions(ABSInitConfig initConfig) {

        final ABSServices services = initConfig.getServices();
        final ABSInfo info = services.getProgramInfo();
        final HistoryLDT historyLDT = services.getTypeConverter()
                .getHistoryLDT();

        final Namespace<SortedOperator> funcNS = initConfig.getServices()
                .getNamespaces().functions();
        Collection<List<DataConstructor>> dataType2ConstructorMap = info
                .getABSParserInfo().getDatatypes()
                .getDataTypes2dataConstructors().values();

        createConstructorFunctions(info, funcNS, dataType2ConstructorMap);

        createConstructorFunctions(info, funcNS, info.getABSParserInfo()
                .getParametricDatatypes().getDataTypes2dataConstructors()
                .values());

        System.out.println("Register Interface Label Constants");

        for (Name itf : info.getABSParserInfo().getInterfaces().keySet()) {
            Function interfaceLabel = new Function(itf,
                    services.getTypeConverter().getHistoryLDT()
                            .getInterfaceLabelSort(), new Sort[0], null, true);
            funcNS.add(interfaceLabel);
        }

        System.out.println("Register Class Label Constants");

        for (Name className : info.getABSParserInfo().getClasses().keySet()) {
            Function classLabel = new Function(className,
                    historyLDT.getClassLabelSort(), new Sort[0], null, true);
            funcNS.add(classLabel);
        }

        System.out.println("Register Method Label Constants");
        // TODO

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
                        final String fullyQualifiedName = c.getModule()
                                .getName()
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
