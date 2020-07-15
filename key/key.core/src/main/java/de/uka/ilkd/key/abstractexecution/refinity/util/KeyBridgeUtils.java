// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.util;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InstantiationChecker;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InstantiationChecker.UnsuccessfulAPERetrievalException;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.Triple;
import recoder.ModelException;

/**
 * Static utilities for interaction with KeY, primarily via .key and .java
 * files.
 * 
 * @author Dominic Steinhoefel
 */
public class KeyBridgeUtils {
    // AE Keywords
    private static final String AE_CONSTRAINT = "ae_constraint";

    // Special Keywords
    private static final String RESULT = "_result";
    private static final String EXC = "_exc";

    public static final java.util.function.Function<String, Collector<String, ?, String>> DL_PREFIX_FOLD = //
            currRes -> Collectors.reducing(currRes,
                    (res, loc) -> prefixOccurrencesWithDL(res, loc));

    private static Optional<Pair<KeYJavaType, Services>> DUMMY_KJT_AND_SERVICES = Optional.empty();

    /////////////// PUBLIC METHODS ///////////////
    
    public static KeYJavaType dummyKJT() {
        return getDummyKJTAndServices().first;
    }

    public static Services dummyServices() {
        return getDummyKJTAndServices().second.copyPreservesLDTInformation();
    }

    public static String jmlStringToJavaDL(String jmlString, final KeYJavaType dummyKJT,
            final Services services) {
        try {
            Term parsed = KeyBridgeUtils.translateJML(jmlString, dummyKJT, services);
            parsed = KeyBridgeUtils.removeLabels(parsed, services);
            return LogicPrinter.quickPrintTerm(parsed, services, false, false);
        } catch (Exception e) {
            throw new RuntimeException("Could not parse JML formula, message: " + e.getMessage(),
                    e);
        }
    }

    public static String dlPrefixRigidModelElements(final List<FunctionDeclaration> locsets,
            final List<PredicateDeclaration> preds, final List<FunctionDeclaration> funcs,
            String result) {
        result = locsets.stream().map(FunctionDeclaration::getFuncName)
                .collect(KeyBridgeUtils.DL_PREFIX_FOLD.apply(result));
        result = funcs.stream().map(FunctionDeclaration::getFuncName)
                .collect(KeyBridgeUtils.DL_PREFIX_FOLD.apply(result));
        result = preds.stream().map(PredicateDeclaration::getPredName)
                .collect(KeyBridgeUtils.DL_PREFIX_FOLD.apply(result));

        return result;
    }

    public static String prefixDLforRE(String str) {
        return Matcher.quoteReplacement(String.format("\\dl_%s", str));
    }

    /**
     * Adds blocks after ae_constraint declarations, escapes abstract functions and
     * predicates, and adds some indentation.
     * 
     * @param javaCode The code to preprocess.
     * @param locsets  Abstract locations sets to escape.
     * @param preds    Abstract predicates to escape.
     * @param funcs    Abstract functions to escape.
     * @return The preprocessed Java code.
     */
    public static String preprocessJavaCode(final String javaCode,
            final List<FunctionDeclaration> locsets, final List<PredicateDeclaration> preds,
            final List<FunctionDeclaration> funcs) {
        /* non_final */ String result = javaCode;

        result = addBlocksAfterConstraints(result);
        result = escapeDL(result, locsets, preds, funcs);
        result = result.replaceAll("\n", "\n        ");

        return result;
    }

    /**
     * Creates premises expressing disjointness of declared abstract location sets
     * with standard variables for result and thrown exception.
     * 
     * @param locsets The declared abstract location sets.
     * @return The additional premises.
     */
    public static String createAdditionalPremises(final List<FunctionDeclaration> locsets) {
        if (locsets.isEmpty()) {
            return "";
        }

        final StringBuilder sb = new StringBuilder();

        for (final FunctionDeclaration decl : locsets) {
            final StringBuilder qfrPrefix = new StringBuilder();
            final List<String> argnames = new ArrayList<>();
            final StringBuilder postfix = new StringBuilder();

            final String argsParams;
            if (!decl.getArgSorts().isEmpty()) {
                int i = 0;
                for (final String type : decl.getArgSorts()) {
                    final String argName = "arg_" + i;

                    qfrPrefix.append("(\\forall ").append(type).append(" ").append(argName)
                            .append("; ");
                    argnames.add(argName);
                    postfix.append(")");
                }

                argsParams = argnames.isEmpty() ? ""
                        : "(" + argnames.stream().collect(Collectors.joining(",")) + ")";
            } else {
                argsParams = "";
            }

            final Consumer<String> appender = var -> {
                sb.append("\n     & ")//
                        .append(qfrPrefix.toString()) //
                        .append("disjoint(singletonPV(") //
                        .append(var) //
                        .append("),") //
                        .append(decl.getFuncName()) //
                        .append(argsParams) //
                        .append(")") //
                        .append(postfix.toString());
            };

            appender.accept(RESULT);
            appender.accept(EXC);
        }

        return sb.toString();
    }

    /**
     * Prefixes variable names in precondition with underscores, and adds \dl_
     * prefixes for rigid model elements, converts JML elements in the precondition
     * to JavaDL elements. Returns "true" for empty precondition.
     * 
     * @param unpreparedJmlPreCondition A JML precondition as input by the user into
     *                                  REFINITY.
     * @param vars
     * @param locsets
     * @param preds
     * @param funcs
     * @param dummyKJT
     * @param services
     * @return A JavaDL precondition from the "unprepared" JML precondition.
     */
    public static String createJavaDLPreCondition(final String unpreparedJmlPreCondition,
            final List<ProgramVariableDeclaration> vars, final List<FunctionDeclaration> locsets,
            final List<PredicateDeclaration> preds, final List<FunctionDeclaration> funcs,
            final KeYJavaType dummyKJT, final Services services) {
        if (unpreparedJmlPreCondition.trim().isEmpty()) {
            // Precondition is optional
            return "true";
        }

        final String jmlPreCondRelation = preparedJMLPreCondition(unpreparedJmlPreCondition, vars,
                locsets, preds, funcs);
        return jmlStringToJavaDL(jmlPreCondRelation, dummyKJT, services);
    }

    /////////////// PRIVATE METHODS ///////////////

    private static Pair<KeYJavaType, Services> getDummyKJTAndServices() {
        if (!DUMMY_KJT_AND_SERVICES.isPresent()) {
            final DummyKeYEnvironmentCreator envCreator = new DummyKeYEnvironmentCreator();
            try {
                envCreator.initialize();
            } catch (ProblemLoaderException | IOException e) {
                throw new RuntimeException(
                        "Could not initialize dummy services, message: " + e.getMessage());
            }

            DUMMY_KJT_AND_SERVICES = Optional
                    .of(new Pair<>(
                            envCreator.getDummyKjt()
                                    .orElseThrow(() -> new RuntimeException(
                                            "Initialization of dummy KJT failed")),
                            envCreator.getDummyServices().orElseThrow(() -> new RuntimeException(
                                    "Initialization of dummy Services failed"))));
        }

        return DUMMY_KJT_AND_SERVICES.orElseThrow(() -> new RuntimeException(
                "Unexpected runtime exception while creating dummy KJT and Services."));
    }

    private static String escapeDL(String prog, final List<FunctionDeclaration> locsets,
            final List<PredicateDeclaration> preds, final List<FunctionDeclaration> funcs) {
        for (final FunctionDeclaration locSet : locsets) {
            prog = prog.replaceAll("\\b" + locSet.getFuncName() + "\\b",
                    Matcher.quoteReplacement("\\dl_" + locSet.getFuncName()));
        }
        for (final PredicateDeclaration predDecl : preds) {
            prog = prog.replaceAll("\\b" + predDecl.getPredName() + "\\b",
                    Matcher.quoteReplacement("\\dl_" + predDecl.getPredName()));
        }

        for (final FunctionDeclaration funcDecl : funcs) {
            prog = prog.replaceAll("\\b" + funcDecl.getFuncName() + "\\b",
                    Matcher.quoteReplacement("\\dl_" + funcDecl.getFuncName()));
        }

        return prog;
    }

    private static Term translateJML(String jmlPostCondRelation, final KeYJavaType dummyKJT,
            final Services services) throws SLTranslationException {
        return JMLTranslator.translate(new PositionedString(jmlPostCondRelation), dummyKJT, null,
                null, null, null, null, null, Term.class, services);
    }

    private static Term removeLabels(final Term term, final Services services) {
        final TermFactory tf = services.getTermFactory();
        return tf.createTerm(term.op(),
                new ImmutableArray<>(term.subs().stream().map(t -> removeLabels(t, services))
                        .collect(Collectors.toList())),
                term.boundVars(), term.javaBlock(), new ImmutableArray<>());
    }

    private static String prefixOccurrencesWithDL(String in, String toPrefix) {
        return in.replaceAll("\\b" + Pattern.quote(toPrefix) + "\\b",
                KeyBridgeUtils.prefixDLforRE(toPrefix));
    }

    private static String addBlocksAfterConstraints(final String javaCode) {
        /* non_final */ String result = javaCode;

        final Pattern aeConstrPattern = Pattern.compile("/\\*@\\s*?" + AE_CONSTRAINT
                + "(.|[\\r\\n])*?\\*/|//@\\s*?" + AE_CONSTRAINT + ".*");
        final Matcher m = aeConstrPattern.matcher(javaCode);

        while (m.find()) {
            final String match = m.group();
            result = result.replaceAll(Pattern.quote(match),
                    Matcher.quoteReplacement(match + "\n{ ; }"));
        }

        return result;
    }

    /**
     * Prefixes variable names in precondition with underscores, and adds \dl_
     * prefixes for rigid model elements.
     * 
     * @param unpreparedJmlPreCondition
     * @param vars
     * @param locsets
     * @param preds
     * @param funcs
     * @return The prepared JML precondition.
     */
    private static String preparedJMLPreCondition(final String unpreparedJmlPreCondition,
            final List<ProgramVariableDeclaration> vars, final List<FunctionDeclaration> locsets,
            final List<PredicateDeclaration> preds, final List<FunctionDeclaration> funcs) {
        String result = unpreparedJmlPreCondition;

        result = vars.stream().map(ProgramVariableDeclaration::getVarName)
                .collect(Collectors.reducing(result, //
                        (res, loc) -> res.replaceAll("\\b" + Pattern.quote(loc) + "\\b",
                                prefixDLforRE("_" + loc))));
        result = dlPrefixRigidModelElements(locsets, preds, funcs, result);

        return result;
    }

    /**
     * Tries to parse the loaded {@link AEInstantiationModel} and returns
     * information about the first found JML/Java error: Message, line, and column
     * number.
     * 
     * @return Information about the first found JML/Java-Error or an empty
     * {@link Optional}.
     */
    public static Optional<Triple<String, Integer, Integer>> getFirstKeYJMLParserErrorMessage(final AEInstantiationModel model) {
        try {
            new InstantiationChecker(model).createRetrievalProof(0);
        } catch (InstantiationChecker.UnsuccessfulAPERetrievalException exc) {
            if (exc.getCause() instanceof ModelException) {
                final ModelException mexc = (ModelException) exc.getCause();
    
                final Pattern p = Pattern.compile("@([0-9]+)/([0-9]+)");
                final Matcher m = p.matcher(mexc.getMessage());
    
                if (!m.matches()) {
                    return Optional.empty();
                }
    
                return Optional.of(new Triple<>(mexc.getMessage(), Integer.parseInt(m.group(1)) - 3,
                        Integer.parseInt(m.group(2)) - 8));
            } else if (exc.getCause() instanceof SLTranslationException) {
                final SLTranslationException slte = (SLTranslationException) exc.getCause();
                return Optional.of(new Triple<>(slte.getMessage(), slte.getPosition().getLine() - 3,
                        slte.getPosition().getColumn() - 8));
            }
        } catch (IOException e) {
            // Some problem occurred... never mind, only for syntax checking
        }
    
        return Optional.empty();
    }

    /**
     * Creates a .key and .java file in a temporary directory based on the supplied
     * contents and initiates a proof. The proof is saved in the temporary directory
     * to a file with the given name.
     * 
     * @param keyFileName Name of the .key file.
     * @param javaSrcDirName Name of the source directory for the Java file (e.g.,
     * "src")
     * @param javaFileName Name of the Java file
     * @param proofFileName Name of the .proof file
     * @param keyFileContent Content of the .key file
     * @param javaFileContent Content of the .java file
     * @param maxRuleApps Number of steps to run. If 0, proof is not started (only
     * root is created), if -1, there is no bound, if > 0, this is the maximum
     * number of rules applied.
     * @return The created proof file.
     * @throws InstantiationChecker.UnsuccessfulAPERetrievalException
     */
    public static Proof createProofAndRun(final String keyFileName, final String javaSrcDirName,
            final String javaFileName, final String proofFileName, final String keyFileContent,
            final String javaFileContent, int maxRuleApps)
            throws InstantiationChecker.UnsuccessfulAPERetrievalException {
        Path tmpDir;
        try {
            tmpDir = Files.createTempDirectory("AEInstCheckerTmp_");
        } catch (IOException e) {
            throw new InstantiationChecker.UnsuccessfulAPERetrievalException("Could not create temporary directory", e);
        }
    
        final Path keyFile = tmpDir.resolve(keyFileName);
        final Path javaSrcDir = tmpDir.resolve(javaSrcDirName);
    
        try {
            Files.write(keyFile, keyFileContent.getBytes());
            Files.createDirectory(javaSrcDir);
            Files.write(javaSrcDir.resolve(javaFileName), javaFileContent.getBytes());
        } catch (IOException e) {
            throw new InstantiationChecker.UnsuccessfulAPERetrievalException(
                    "Could not write KeY problem file for retrieval", e);
        }
    
        KeYEnvironment<?> env;
        try {
            env = KeYEnvironment.load(JavaProfile.getDefaultInstance(), keyFile.toFile(),
                    Collections.emptyList(), null, Collections.emptyList(), false);
        } catch (ProblemLoaderException e) {
            throw new InstantiationChecker.UnsuccessfulAPERetrievalException("Could not load KeY problem",
                    MiscTools.findExceptionCauseOfClass(SLTranslationException.class, e)
                            .map(Throwable.class::cast)
                            .orElse(MiscTools.findExceptionCauseOfClass(ModelException.class, e)
                                    .map(Throwable.class::cast).orElse(e)));
        }
    
        final Proof proof = env.getLoadedProof();
    
        if (maxRuleApps != 0) {
            final ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.setMaxRuleApplications(maxRuleApps);
            starter.start();
        }
    
        try {
            proof.saveToFile(tmpDir.resolve(proofFileName).toFile());
        } catch (IOException e) {
            throw new InstantiationChecker.UnsuccessfulAPERetrievalException("Could not save proof", e);
        }
    
        return proof;
    }

}
