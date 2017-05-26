// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.analyzer;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.util.InformationExtraction;
import de.tud.cs.se.ds.specstr.util.Utilities;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class Analyzer {
    private static final Logger logger = LogManager.getFormatterLogger();

    private File file;
    private String className, methodName, methodTypeStr;
    private KeYEnvironment<DefaultUserInterfaceControl> environment;

    public Analyzer(File file, String method) throws ProblemLoaderException {
        this.file = file;
        if (!parseMethodString(method)) {
            final String errorMsg = Utilities
                    .format("Error in parsing method descriptor %s", method);
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        logger.trace("Building KeY environment for file %s", file);
        // @formatter:off
        environment = KeYEnvironment.load(
//                JavaProfile.getDefaultInstance(),
                SymbolicExecutionJavaProfile.getDefaultInstance(),
                file,     // location
                null,     // class path
                null,     // boot class path
                null,     // includes
                true);    // forceNewProfileOfNewProofs
        // @formatter:on
        logger.trace("Built up environment.");
    }

    public AnalyzerResult analyze() {
        logger.info("Analyzing Java file %s", file);

        List<KeYJavaType> declaredTypes = InformationExtraction
                .getDeclaredTypes(environment);

        assert declaredTypes
                .size() > 0 : "Unexpectedly, no type is declared in the supplied Java file.";

        List<ClassDeclaration> matchingClassDecls = declaredTypes.stream()
                .filter(t -> t.getJavaType().getFullName().equals(className))
                .filter(t -> t.getJavaType() instanceof ClassDeclaration)
                .map(t -> (ClassDeclaration) t.getJavaType())
                .collect(Collectors.toList());

        if (matchingClassDecls.isEmpty()) {
            final String errorMsg = Utilities.format(
                    "Could not find type %s in class %s", className,
                    file.getName());
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        assert declaredTypes
                .size() == 1 : "There should be only one type of a given name";

        List<ProgramMethod> matchingMethods = Utilities
                .toStream(matchingClassDecls.get(0).getMembers())
                .filter(m -> m instanceof ProgramMethod)
                .map(m -> (ProgramMethod) m)
                .filter(m -> m.getName().equals(methodName))
                .filter(m -> InformationExtraction.getMethodTypeDescriptor(m)
                        .equals(methodTypeStr))
                .collect(Collectors.toList());

        if (matchingMethods.isEmpty()) {
            final String errorMsg = Utilities.format(
                    "Could not find method %s%s in class %s", className,
                    methodTypeStr, file.getName());
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        assert matchingMethods
                .size() == 1 : "There should be only one method of a given signature";

        final ProgramMethod method = matchingMethods.get(0);

        SymbExInterface seIf = new SymbExInterface(environment);

        // Run until while loop
        final Goal whileGoal = seIf.runUntilLoop(method);
        final Node whileNode = whileGoal.node();

        // Apply loop invariant rule
        SequentFormula whileSeqFor = Utilities
                .toStream(whileGoal.node().sequent().succedent())
                .filter(f -> SymbolicExecutionUtil
                        .hasSymbolicExecutionLabel(f.formula()))
                .filter(f -> JavaTools.getActiveStatement(
                        TermBuilder.goBelowUpdates(f.formula())
                                .javaBlock()) instanceof While)
                .findFirst().get();

        PosInOccurrence whilePio = new PosInOccurrence(whileSeqFor,
                PosInTerm.getTopLevel(), false);
        whileGoal.apply(LoopScopeInvariantRule.INSTANCE
                .createApp(whilePio, whileGoal.proof().getServices())
                .tryToInstantiate(whileGoal));

        // Try to close first open goal
        seIf.applyMacro(new TryCloseMacro(1000), whileNode.child(0));

        if (!whileNode.child(0).isClosed()) {
            logger.warn("The loop's invariant is not initially valid");
        }

        // Finish symbolic execution for second open goal
        final Node preservesAndUCNode = whileNode.child(1);
        seIf.applyMacro(new FinishSymbolicExecutionMacro(), preservesAndUCNode);

        ImmutableList<Goal> openSubtreeGoals = whileGoal.proof()
                .getSubtreeGoals(preservesAndUCNode);

        // TODO: Treat invalid invariants specially
        logger.info("Invariant to weak for %s goals (or invalid)"
                + openSubtreeGoals.size());

        // Try to close remaining open goals
        seIf.applyMacro(new TryCloseMacro(10000), preservesAndUCNode);

        // Apply OSS to the remaining open goals

        // Construct "psi"

        // XXX Test Code -->
        try {
            whileGoal.proof().saveToFile(new File("inclLoop.proof"));
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        // XXX <-- Test Code

        logger.info("Finished analysis of Java file %s", file);
        return null;
    }

    private boolean parseMethodString(String methodStr) {
        // @ formatter:off
        // Expected format:
        //
        // <fully qualified type name>::<method name>(<arg decl>)<return type
        // decl>
        //
        // where <arg decl> is according to the field descriptors
        // in the JVM specification, for instance
        //
        // [ILjava.lang.Object;D
        //
        // for an integer array, an Object and a double (not that
        // we would support doubles...). <return type decl> is
        // constructed similarly, only for a single type.
        // @ formatter:on

        Pattern p = Pattern.compile("^([^:]*)::([^\\(]*)(\\([^\\)]*\\).*)$");
        Matcher m = p.matcher(methodStr);

        if (!m.matches() || m.groupCount() != 3) {
            return false;
        }

        className = m.group(1);
        methodName = m.group(2);
        methodTypeStr = m.group(3);

        return true;
    }

    class AnalyzerResult {
        private final int loopInvStrength;

        public AnalyzerResult(int loopInvStrength) {
            this.loopInvStrength = loopInvStrength;
        }

        public int getLoopInvStrength() {
            return loopInvStrength;
        }
    }

}
