package de.uka.ilkd.keyabs.abs.converter;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.HashMap;

import abs.backend.coreabs.CoreAbsBackend;
import abs.frontend.ast.ASTNode;
import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.DataTypeDecl;
import abs.frontend.ast.FunctionDecl;
import abs.frontend.ast.InterfaceDecl;
import abs.frontend.ast.List;
import abs.frontend.ast.Model;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.proof.JavaModel;

public class ABSModelParserInfo {

	private final HashMap<ProgramElementName, InterfaceDecl> interfaces = new HashMap<ProgramElementName, InterfaceDecl>();
	private final HashMap<ProgramElementName, DataTypeDecl> datatypes = new HashMap<ProgramElementName, DataTypeDecl>();
	private final HashMap<ProgramElementName, List<DataConstructor>> dataTypes2dataConstructors = new HashMap<ProgramElementName, List<DataConstructor>>();

	private final CoreAbsBackend absBackend;
	private String sourceDirectory;
	private String[] compilationUnitsFiles;
	private JavaModel absModelDescription;
	private boolean alreadyParsed;
	private Model absModel;


	public HashMap<ProgramElementName, InterfaceDecl> getInterfaces() {
		return interfaces;
	}

	public HashMap<ProgramElementName, DataTypeDecl> getDatatypes() {
		return datatypes;
	}

	public HashMap<ProgramElementName, List<DataConstructor>> getDataTypes2dataConstructors() {
		return dataTypes2dataConstructors;
	}

	public ABSModelParserInfo() {
		this.absBackend = new CoreAbsBackend();

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
			for (int i = 0; i<child.getNumChild(); i++) {
				ASTNode<?> currentNode = child.getChild(i);
				if (currentNode instanceof InterfaceDecl) {
					final InterfaceDecl interf = (InterfaceDecl) currentNode;                  
					interfaces.put(new ProgramElementName(interf.getName(), interf.getModule().getName()), interf);
				} else if (currentNode instanceof DataTypeDecl) {                    
					final DataTypeDecl dataType = (DataTypeDecl) currentNode;
					final ProgramElementName dataTypeName = new ProgramElementName(dataType.getName(), dataType.getModule().getName());
					datatypes.put(dataTypeName, dataType);

					collectConstructors(dataType, dataTypeName);                    
					System.out.println("Found datatype: "+dataType.getName() + ":" +dataType.getModule().getName());
				} else if (currentNode instanceof FunctionDecl) { 
					FunctionDecl fd = (FunctionDecl)currentNode;
					System.out.println(fd.getName() + ":" + fd.qualifiedName() + ":::" + fd.getParamList() + ":::" + fd.getTypeUse() + ":::" + fd.getTypeUse().getDecl().isTypeParameter());
				} else {
					collectTypesAndFunctionDeclarations(currentNode);
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
