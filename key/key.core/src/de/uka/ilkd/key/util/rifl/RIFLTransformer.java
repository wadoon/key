// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.rifl;

import java.io.*;
import javax.xml.parsers.*;
import javax.xml.validation.Schema;
import javax.xml.validation.Validator;
import javax.xml.validation.ValidatorHandler;

import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.util.Debug;
import org.xml.sax.*;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.java.CompilationUnit;
import recoder.java.JavaProgramFactory;
import de.uka.ilkd.key.util.DirectoryFileCollection;
import de.uka.ilkd.key.util.FileCollection.Walker;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.util.Pair;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;

/**
 * Facet class for interpreting RIFL specifications. The Requirements for
 * Information Flow Language (RIFL) is a tool-independent specification language
 * developed in the RS3 project. Method <code>transform</code> reads a RIFL file
 * and Java sources and writes JML* information flow specifications to the
 * original Java files.
 * <p>
 * <b>changes (weigl, 2016-08-16):</b> changed interfaces to File. This avoid
 * some crud string operations on filenames, remove threads and simplify things.
 *
 * @author bruns
 * @author weigl, 2016-08-17
 */
public class RIFLTransformer {
	private List<File> result = new ArrayList<>();
	private boolean verbose;
	private String blueprint;

	public RIFLTransformer() throws ParserConfigurationException, SAXException, IOException {
		JPF.initialize(new CrossReferenceServiceConfiguration());
		assert JPF.getServiceConfiguration() != null;

		String tmp = "";
		BufferedReader br = new BufferedReader(
				new InputStreamReader(getClass().getResourceAsStream("blueprint_rifl.key")));
		while ((tmp = br.readLine()) != null) {
			blueprint += tmp + "\n";
		}
	}

	// private static final String TMP_PATH =
	// System.getProperty("java.io.tmpdir");
	private static final JavaProgramFactory JPF = de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory.getInstance();

	/**
	 * Entry point for the stand-alone RIFL to JML* tool.
	 * @throws ParserConfigurationException 
	 * @throws ParserException 
	 * @throws SAXException 
	 * @throws IOException 
	 */
	public static void main(String[] args) throws IOException, SAXException, ParserException, ParserConfigurationException {
		if (args.length < 2 || "--help".equals(args[0])) {
			System.out.println("This is the RIFL to JML* transformer.");
			System.out.println("Usage: <RIFL file> <Java sources>");
		} else {
			final File riflFilename = new File(args[0]);
			final File javaFilename = new File(args[1]);
			RIFLTransformer transformer = new RIFLTransformer();
			transformer.doTransform(riflFilename, javaFilename);
		}
	}
	
	/**
	 * Returns the default save path for transformed Java files.
	 *
	 * @param origSourcePath
	 *            path to a directory or single Java file
	 * @return path to the transformed directory
	 */
	public static File getDefaultSavePath(File origSourcePath) {
		// TODO weigl: Shouldn't we use the old directory, because of reference
		// to other java files?
		origSourcePath = getBaseDirPath(origSourcePath);
		return new File(origSourcePath.getParentFile(), origSourcePath.getName() + "_RIFL");
	}

	private static File getBaseDirPath(File origSourcePath) {
		if (origSourcePath.isFile())
			return origSourcePath.getParentFile();
		else
			return origSourcePath;
	}

	private Map<CompilationUnit, File> readJava(File root) throws IOException, ParserException {
		assert root.exists() : "source dir must exist";
		assert root.isDirectory() : "source must be directory";
		final DirectoryFileCollection files = new DirectoryFileCollection(root);
		final Walker walker = files.createWalker(".java");

		final ServiceConfiguration serviceConfiguration = JPF.getServiceConfiguration();
		Map<CompilationUnit, File> javaCUs = new HashMap<CompilationUnit, File>();

		// parse
		while (walker.step()) {
			final File javaFile = new File(walker.getCurrentName());
			// debug
			if (Debug.ENABLE_DEBUG) {
				System.out.println("[RIFL] Read file: " + javaFile);
			}

			final CompilationUnit cu;
			Reader fr = null;

			try {
				fr = new BufferedReader(new FileReader(javaFile));
				cu = JPF.parseCompilationUnit(fr);

				// crud relative
				File relative = relative(root, javaFile);
				javaCUs.put(cu, relative); // relative path
				serviceConfiguration.getChangeHistory().updateModel(); // workaround
																		// to an
																		// issue
																		// in
																		// recoder
			} catch (IOException e) {
				throw e;
			} catch (ParserException e) {
				throw e;
			} finally {
				if (fr != null)
					fr.close();
			}
		}
		return javaCUs;
	}

	private File relative(File root, File javaFile) {
		return new File(javaFile.getAbsolutePath().substring(root.getAbsolutePath().length()));
	}

	private SpecificationContainer readRIFL(File fileName)
			throws IOException, SAXException, ParserConfigurationException {
		final SAXParserFactory spf = SAXParserFactory.newInstance();
		spf.setNamespaceAware(true);
		spf.setValidating(true);
		SAXParser saxParser = spf.newSAXParser();
		XMLReader xmlReader = saxParser.getXMLReader();
		xmlReader.setContentHandler(new RIFLHandler());
		xmlReader.setErrorHandler(new RIFLHandler.ErrorHandler());
		xmlReader.parse(fileName.toURI().toString());
		return ((RIFLHandler) xmlReader.getContentHandler()).getSpecification();
	}

	/**
	 * 
	 * @param riflFilename
	 *            path to the rifl file
	 * @param source
	 *            path to the java source file
	 * @throws IOException
	 * @throws SAXException
	 * @throws ParserException
	 * @throws ParserConfigurationException
	 */
	public void doTransform(final File riflFilename, final File source)
			throws IOException, SAXException, ParserException, ParserConfigurationException {
		File savePath = getDefaultSavePath(source);
		ensureTargetDirExists(savePath);
		final File javaRoot = getBaseDirPath(source);

		// step 1: read files
		SpecificationContainer sc = readRIFL(riflFilename);
		Map<CompilationUnit, File> javaCUs = readJava(javaRoot);

		// step 2: inject specifications
		// TODO rename the public class in the compilation unit and reuse the
		// old java folder, for ensure interdepences to other files
		int counter = 0;
		for (CompilationUnit cu : javaCUs.keySet()) {
			final SpecificationInjector si = new SpecificationInjector(sc,
					JPF.getServiceConfiguration().getSourceInfo());
			cu.accept(si);

			ClassDeclaration clazz = (ClassDeclaration) cu.getPrimaryTypeDeclaration();
			for (recoder.abstraction.Method targetMethod : clazz.getAllMethods()) {
				if (targetMethod instanceof MethodDeclaration) {
					MethodDeclaration mdecl = (MethodDeclaration) targetMethod;

					// create type names, e.g. 'int,int'
					StringBuilder sb = new StringBuilder();
					{
						for (ParameterDeclaration p : mdecl.getParameters()) {
							sb.append(p.getTypeReference().getName());
							sb.append(",");
						}
						sb.deleteCharAt(sb.length() - 1);
					}

					String poname = String.format("%s[%s\\\\:\\\\:%s(%s).Non-interference contract.0",
							clazz.getFullName(), clazz.getFullName(), targetMethod.getName(), sb);

					File problemFileName = new File(javaRoot.getParent(),
							riflFilename.getName() + "_" + counter++ + ".key");

					writeProblemFile(problemFileName, getDefaultSavePath(javaRoot).getName(), poname);

					if (verbose) {
						System.out.format("[RIFL] generate problem file '%s' for method %s.%s(%s)%n", problemFileName,
								clazz.getFullName(), targetMethod, sb);
					}

					result.add(problemFileName);
				}
			}
		}

		// step 3: write modified Java files
		for (Map.Entry<CompilationUnit, File> javaUnit : javaCUs.entrySet()) {
			CompilationUnit cu = javaUnit.getKey();
			File relative = javaUnit.getValue();
			File target = new File(savePath, relative.toString());
			writeJavaFile(target, cu);

			if (verbose) {
				System.out.format("[RIFL] write annotated java source to '%s' %n", target);
			}
		}

	}

	private void writeProblemFile(File problemFileName, String newJavaFolder, String poname) {
		try {
			FileWriter fw = new FileWriter(problemFileName);
			fw.write(blueprint.replaceAll("%%JAVA_SOURCE%%", newJavaFolder).replaceAll("%%PO_NAME%%", poname));			
			fw.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private void ensureTargetDirExists(File target) throws IOException {
		if (target.exists()) {
			if (target.isDirectory() && target.canWrite()) {
				return; // nothing to do
			} else { // bad
				throw new IOException("target directory " + target + " not writable");
			}
		} else { // create directory
			target.mkdir();
		}
	}

	/**
	 * Writes a single Java file.
	 */
	private void writeJavaFile(File target, CompilationUnit cu) throws IOException {
		FileWriter writer = null;
		try {
			if (Debug.ENABLE_DEBUG) {
				System.out.println("[RIFL] Trying to write file " + target);
			}

			writer = new FileWriter(target);
			final String source = cu.toSource();

			if (Debug.ENABLE_DEBUG) {
				System.out.println("[RIFL] Write the following contents to file:");
				System.out.println(source);
			}

			writer.write(source);
			writer.flush();
		} finally {
			if (writer != null)
				writer.close();
		}
	}

	public List<File> getProblemFiles() {
		return result;
	}

	public void setVerbosity(boolean b) {
		verbose = b;

	}
}