package de.uka.ilkd.keyabs.abs.converter;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map.Entry;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.ASTNode;
import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.DataTypeDecl;
import abs.frontend.ast.FunctionDecl;
import abs.frontend.ast.InterfaceDecl;
import abs.frontend.ast.InterfaceTypeUse;
import abs.frontend.ast.List;
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

	private static final Name ABS_BOOLEAN_TYPE_NAME = new Name(
			"ABS.StdLib.Bool");
	private static final Name ABS_INT_TYPE_NAME = new Name("ABS.StdLib.Int");
	private final HashMap<Name, InterfaceDecl> interfaces = new HashMap<Name, InterfaceDecl>();
	private final HashMap<Name, DataTypeDecl> datatypes = new HashMap<Name, DataTypeDecl>();
	private final HashMap<Name,ParametricDataTypeDecl> parametricDatatypes = new HashMap<Name, ParametricDataTypeDecl>();
	private final HashMap<Name, List<DataConstructor>> dataTypes2dataConstructors = new HashMap<Name, List<DataConstructor>>();

	private final CoreAbsBackend absBackend;
	private String sourceDirectory;
	private String[] compilationUnitsFiles;
	private JavaModel absModelDescription;
	private boolean alreadyParsed;
	private Model absModel;

	public HashMap<Name, InterfaceDecl> getInterfaces() {
		return interfaces;
	}

	public HashMap<Name, DataTypeDecl> getDatatypes() {
		return datatypes;
	}

	public HashMap<Name,ParametricDataTypeDecl> getParametricDatatypes() {
		return parametricDatatypes;
	}

	public HashMap<Name, List<DataConstructor>> getDataTypes2dataConstructors() {
		return dataTypes2dataConstructors;
	}

	public ABSModelParserInfo() {
		this.absBackend = new CoreAbsBackend();
		this.absBackend.setWithStdLib(true);
	}

	public void setup(JavaModel absModel) {
		this.absModelDescription = absModel;
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

	public void readABSModel() throws IOException {
		if (!alreadyParsed && compilationUnitsFiles != null) {
			absModel = absBackend.parseFiles(compilationUnitsFiles);
			collectTypesAndFunctionDeclarations(absModel);
			alreadyParsed = true;
		}
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
					final Name dataTypeName = new Name(createFullyQualifiedName(dataType));
				
					if (dataType.getNumTypeParameter() > 0) {
						System.out.println("===> " + dataType.getClass() + " PARAMETRIC "+dataType.getType());
						parametricDatatypes.put(dataTypeName, (ParametricDataTypeDecl)dataType);
					} else {
						datatypes.put(dataTypeName, dataType);
					}
					collectConstructors(dataType, dataTypeName);
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

	private String createFullyQualifiedName(final TypeDecl interf) {
		return interf.getModule().getName() + "." + interf.getName();
	}

	private void collectConstructors(DataTypeDecl decl, Name dataTypeName) {
		List<DataConstructor> constructors = decl.getDataConstructors();
		dataTypes2dataConstructors.put(dataTypeName, constructors);

	}

	public void finish(IServices iServices) {
		// create KeYJavaTypes and put them in map
		registerAndCreateABSInterfaceType2SortMapping(iServices);
		registerAndCreateABSDataType2SortMapping(iServices);

	}

	private void registerAndCreateABSDataType2SortMapping(IServices iServices) {
		Sort topSort = (Sort) iServices.getNamespaces().sorts()
				.lookup(new Name("any"));

		assert topSort != null;

		for (Entry<Name, DataTypeDecl> dataType : datatypes.entrySet()) {
			final ABSDatatype absType = new ABSDatatype(dataType.getKey());
			Sort dataTypeSort = (Sort) iServices.getNamespaces().sorts()
					.lookup(dataType.getKey());
			if (dataTypeSort == null) {
				checkBuiltInType(iServices, dataType);
				dataTypeSort = new SortImpl(dataType.getKey(), topSort);
			}

			final KeYJavaType abs2sort = new KeYJavaType(absType, dataTypeSort);
			iServices.getProgramInfo().rec2key().put(absType, abs2sort);
		}
	}

	private void checkBuiltInType(IServices iServices,
			Entry<Name, DataTypeDecl> dataType) {
		Sort dataTypeSort;
		if (dataType.getKey().equals(ABS_INT_TYPE_NAME)) {
			dataTypeSort = (Sort) iServices.getNamespaces().sorts()
					.lookup(new Name("int"));
		} else if (dataType.getKey().equals(ABS_BOOLEAN_TYPE_NAME)) {
			dataTypeSort = (Sort) iServices.getNamespaces().sorts()
					.lookup(new Name("boolean"));
		}
	}

	private void registerAndCreateABSInterfaceType2SortMapping(
			IServices iServices) {
		Sort anyInterfaceSort = (Sort) iServices.getNamespaces().sorts()
				.lookup(new ProgramElementName("ABSAnyInterface"));

		assert anyInterfaceSort != null;

		@SuppressWarnings("unchecked")
		Entry<Name, InterfaceDecl>[] interfArray = sortInterfacesAscendingInNumberOfExtendedTypes();

		final HashMap<Name, KeYJavaType> names2type = new HashMap<>();

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

	private ImmutableSet<Sort> createListOfExtendedSortsFromTypeDeclaration(
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

	private String createFullyQualifiedName(InterfaceTypeUse ifdecl) {
		return ifdecl.getModuleDecl().getName() + "." + ifdecl.getName();
	}

}
