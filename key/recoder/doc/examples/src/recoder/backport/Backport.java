package recoder.backport;

import java.io.File;
import java.io.IOException;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.PropertyNames;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.kit.transformation.java5to4.EnhancedFor2For;
import recoder.kit.transformation.java5to4.MakeConditionalCompatible;
import recoder.kit.transformation.java5to4.RemoveAnnotations;
import recoder.kit.transformation.java5to4.RemoveCoVariantReturnTypes;
import recoder.kit.transformation.java5to4.RemoveStaticImports;
import recoder.kit.transformation.java5to4.ReplaceEnums;
import recoder.kit.transformation.java5to4.ResolveBoxing;
import recoder.kit.transformation.java5to4.ResolveGenerics;
import recoder.kit.transformation.java5to4.ResolveVarArgs;
import recoder.kit.transformation.java5to4.methodRepl.ReplaceEmptyCollections;

public class Backport {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		if (args.length != 2) {
			System.out.println("Usage: backport.Backport input-path output-path");
			System.out.println("WARNING: If target files exist, they will be overwritten without further notice!");
			System.out.println("Current runtime classes will be used if no rt.jar is specified in input path");
			System.out.println("");
			System.out.println("See http://recoder.sourceforge.net for more details");
			return;
		}

		CrossReferenceServiceConfiguration crsc = new CrossReferenceServiceConfiguration();
		SourceFileRepository dsfr = crsc.getSourceFileRepository();
		
		String outPath = args[1];
		if(!(new File(outPath).isDirectory())) {
			if (!new File(outPath).mkdir()) {
				System.out.println("ERROR: specified output-path is not a directory" +
						" and could not be created either");
				return;
			}
		}

		crsc.getProjectSettings().setProperty(PropertyNames.INPUT_PATH, args[0]);
		crsc.getProjectSettings().setProperty(PropertyNames.OUTPUT_PATH, outPath);
		crsc.getProjectSettings().setProperty(PropertyNames.JAVA_5, "true");
        crsc.getProjectSettings().setProperty(PropertyNames.TABSIZE, "4");
     	if (!crsc.getProjectSettings().ensureSystemClassesAreInPath()) {
     		System.out.println("\tWarning: Cannot find system classe (rt.jar)");
     		System.out.println("\tThis will likely cause an error, unless you are");
     		System.out.println("\ttrying to transform the JDK itself. Please make sure");
     		System.out.println("\tthat java.home is set, or specify an rt.jar in the");
     		System.out.println("\tinput classpath.");
     	}
        
     	
     	System.out.println("Now parsing source files. This may take a while...");
     	
        try {
            dsfr.getAllCompilationUnitsFromPath();
            System.out.println("Parsing done. Now updating model. This may take a while...");
            crsc.getChangeHistory().updateModel();
        } catch (ParserException pe) {
            System.out.println(pe.getMessage());
            System.out.println("Parse error. Aborting.");
            return;
        }
        List<CompilationUnit> cul = dsfr.getCompilationUnits();
        for (CompilationUnit cu : cul) {
        	// just to make sure...
        	cu.validateAll();
        }
        
        System.out.println("Beginning transformations...");
		
		System.out.println("Conditionals");
    	MakeConditionalCompatible mcc = new MakeConditionalCompatible(crsc, cul);
    	mcc.execute();
    	
    	System.out.println("Enhanced For");
    	EnhancedFor2For eff = new EnhancedFor2For(crsc, cul);
    	eff.execute();
    	
    	System.out.println("Generics");
    	ResolveGenerics rg = new ResolveGenerics(crsc, cul);
    	rg.execute();
    	
    	System.out.println("Covariant Return Types");
    	RemoveCoVariantReturnTypes rc = new RemoveCoVariantReturnTypes(crsc, cul);
    	rc.execute();
    	
    	System.out.println("Annotations");
    	RemoveAnnotations ra = new RemoveAnnotations(crsc, cul);
    	ra.execute();
    	
    	System.out.println("Static Imports");
    	RemoveStaticImports rsi = new RemoveStaticImports(crsc, cul);
    	rsi.execute();
    	
    	System.out.println("Boxing");
    	ResolveBoxing rb = new ResolveBoxing(crsc, cul);
    	rb.execute();
    	
    	System.out.println("Varargs");
    	ResolveVarArgs rva = new ResolveVarArgs(crsc, cul);
    	rva.execute();
    	
    	System.out.println("Enumerations");
    	ReplaceEnums re = new ReplaceEnums(crsc, cul);
    	re.execute();
    	
    	System.out.println("ReplaceEmptyCollection");
    	ReplaceEmptyCollections rec = new ReplaceEmptyCollections(crsc);
    	rec.execute();
    	
    	System.out.println("Done transforming. now writing back files.");
    	
        try {
            dsfr.printAll(true);
        } catch (IOException e) {
            System.out.println(e.getMessage());
        	System.out.println("IOException while writing back files...");
        	return;
        }
        System.out.println("Done.");
	}

}
