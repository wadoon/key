// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;

import java.util.stream.Collectors;

import org.key_project.util.Filenames;
import org.key_project.util.Strings;
import org.key_project.util.collection.*;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.FilterVisitor;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.RenamingTable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * Collection of some common, stateless functionality. Originally stolen from
 * the weissInvariants side branch.
 */
public final class MiscTools {

    private MiscTools() {
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    // TODO Is rp always a program variable?
    public static ProgramVariable getSelf(MethodFrame mf) {
        ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if (!(rp instanceof TypeReference) && rp != null) {
            return (ProgramVariable) rp;
        } else {
            return null;
        }
    }

    /**
     * Returns the receiver term of the passed method frame, or null if the frame belongs to a
     * static method.
     *
     * @param mf a method frame.
     * @param services services.
     * @return the receiver term of the passed method frame, or null if the frame belongs to a
     * static method.
     */
    public static Term getSelfTerm(MethodFrame mf, Services services) {
        ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if (!(rp instanceof TypeReference) && rp != null) {
            return services.getTypeConverter().convertToLogicElement(rp);
        } else {
            return null;
        }
    }

    /**
     * All variables read in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables read in the specified program element,
     *  excluding newly declared variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalIns(ProgramElement pe,
            Services services) {
        final ReadPVCollector rpvc = new ReadPVCollector(pe, services);
        rpvc.start();
        return rpvc.result();
    }

    /**
     * All variables changed in the specified program element, excluding newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element,
     *  excluding newly declared variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOuts(
            ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getWrittenPVs();
    }

    /**
     * All variables changed in the specified program element, including newly declared variables.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables changed in the specified program element,
     *  including newly declared variables.
     */
    public static ImmutableSet<ProgramVariable> getLocalOutsAndDeclared(
            ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getWrittenPVs().union(wpvc.getDeclaredPVs());
    }

    /**
     * All variables newly declared in the specified program element.
     *
     * @param pe a program element.
     * @param services services.
     * @return all variables newly declared in the specified program element.
     */
    public static ImmutableSet<ProgramVariable> getLocallyDeclaredVars(
            ProgramElement pe,
            Services services) {
        final WrittenAndDeclaredPVCollector wpvc = new WrittenAndDeclaredPVCollector(pe, services);
        wpvc.start();
        return wpvc.getDeclaredPVs();
    }

    /**
     * Recursively collect all observers for this term including all of its sub terms.
     * @param t the term for which we want to collect the observer functions.
     * @return the observers as a set of pairs with sorts and according observers
     */
    public static ImmutableSet<Pair<Sort, IObserverFunction>> collectObservers(Term t) {
        ImmutableSet<Pair<Sort, IObserverFunction>> result = DefaultImmutableSet.nil();
        if (t.op() instanceof IObserverFunction) {
            final IObserverFunction obs = (IObserverFunction) t.op();
            final Sort s = obs.isStatic()
                    ? obs.getContainerType().getSort()
                    : t.sub(1).sort();
            result = result.add(new Pair<Sort, IObserverFunction>(s, obs));
        }
        for (Term sub : t.subs()) {
            result = result.union(collectObservers(sub));
        }
        return result;
    }


    /**
     * True if both are <code>null</code> or <code>a.equals(b)</code> with <code>equals</code> from type T.
     * You should use {@link Objects#equals(Object, Object)} directly.
     */
    @Deprecated
    public static <T> boolean equalsOrNull(T a, Object b) {
        return Objects.equals(a, b);
        /*if (a == null) {
            return b == null;
        } else {
            return a.equals(b);
        }*/
    }

    /**
     * {@code true} iff all are <code>null</code> or <code>a.equals(b)</code>
     * with <code>equals</code> from type T for every {@code b}.
     *
     * @param a an object.
     * @param bs other object.
     * @param <T> type of {@code a} and result value.
     * @return {@code true} iff all are <code>null</code> or <code>a.equals(b)</code>
     *  with <code>equals</code> from type T for every {@code b}.
     */
    public static <T> boolean equalsOrNull(T a, Object... bs) {
        boolean result = true;
        for (Object b : bs) {
            result = result && equalsOrNull(a, b);
        }
        return result;
    }

    // =======================================================
    // Methods operating on Arrays
    // =======================================================

    /**
     * Concatenates two arrays.
     *
     * @param s1 an array.
     * @param s2 another array.
     * @param <S> type o array {@code s1} and of result array.
     * @param <T> type of array {@code s2}.
     * @return the concatenation of both arrays.
     */
    public static <S, T extends S> S[] concat(S[] s1, T[] s2) {
        return KeYCollections.concat(s1,s2);
    }

    // =======================================================
    // Methods operating on Collections
    // =======================================================

    /**
     * Combine two maps by function application. Values of <code>m0</code> which are not keys of
     * <code>m1</code> are dropped. This implementation tries to use the same implementation of
     * {@link java.util.Map} (provided in Java SE) as <code>m0</code>.
     *
     * @param m0 a map.
     * @param m1 another map.
     * @param <S> type of {@code m0}.
     * @param <T> type of {@code m1}.
     * @param <U> new type of result map indexes.
     * @return the combination of both maps.
     */
    public static <S, T, U> Map<S, U> apply(Map<S, ? extends T> m0, Map<T, U> m1) {
        return KeYCollections.apply(m0, m1);
    }

    // =======================================================
    // Methods operating on Strings
    // =======================================================

    /**
     * Separates the single directory entries in a filename. The first element is an empty String
     * iff the filename is absolute. (For a Windows filename, it contains a drive letter and a
     * colon). Ignores double slashes and slashes at the end, removes references to the cwd. E.g.,
     * "/home//daniel/./key/" yields {"","home","daniel","key"}. Tries to automatically detect UNIX
     * or Windows directory delimiters. There is no check whether all other characters are valid for
     * filenames.
     *
     * @param filename a file name.
     * @return all directory entries in the file name.
     */
    static List<String> disectFilename(String filename) {
        return Filenames.disectFilename(filename);
    }

    /**
     * Returns a filename relative to another one. The second parameter needs to be absolute and is
     * expected to refer to a directory. This method only operates on Strings, not on real files!
     * Note that it treats Strings case-sensitive. The resulting filename always uses UNIX
     * directory delimiters. Raises a RuntimeException if no relative path could be found (may
     * happen on Windows systems).
     *
     * @param origFilename a filename.
     * @param toFilename the name of a parent directory of {@code origFilename}.
     * @return {@code origFilename} relative to {@code toFilename}
     */
    public static String makeFilenameRelative(String origFilename, String toFilename) {
        return Filenames.makeFilenameRelative(origFilename, toFilename);
    }

    public static Name toValidTacletName(String s) {
        s = s.replaceAll("\\s|\\.|::\\$|::|<|>|/", "_");
        return new Name(s);
    }

    public static String toValidFileName(String s) {
        s = s.replace("\\", "_")
                .replace("$", "_")
                .replace("?", "_")
                .replace("|", "_")
                .replace("<", "_")
                .replace(">", "_")
                .replace(":", "_")
                .replace("*", "+")
                .replace("\"", "'")
                .replace("/", "-")
                .replace("[", "(")
                .replace("]", ")");
        return s;
    }

    public static Name toValidVariableName(String s) {
        s = s.replaceAll("\\s|\\.|::\\$|::|<|>|/|\\(|\\)|,", "_");
        return new Name(s);
    }

    /**
     * Join the string representations of a collection of objects into onw string. The individual
     * elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null collection
     * @param delimiter  a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the delimiter
     */
    public static String join(Iterable<?> collection, String delimiter) {
        return KeYCollections.join(collection, delimiter);
    }

    /**
     * Join the string representations of an array of objects into one string. The individual
     * elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection an arbitrary non-null array of objects
     * @param delimiter  a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the delimiter
     */
    public static String join(Object[] collection, String delimiter) {
        return KeYCollections.join(collection, delimiter);
    }

    /**
     * Takes a string and returns a string which is potentially shorter and contains a
     * sub-collection of the original characters.
     *
     * All alphabetic characters (A-Z and a-z) are copied to the result while all other characters
     * are removed.
     *
     * @param string an arbitrary string
     * @return a string which is a sub-structure of the original character sequence
     *
     * @author Mattias Ulbrich
     */
    public static /* @ non_null @ */ String filterAlphabetic(/* @ non_null @ */ String string) {
        return KeYCollections.filterAlphabetic(string);
    }

    /**
     * Checks whether a string contains another one as a whole word (i.e., separated by
     * white spaces or a semicolon at the end).
     *
     * @param s    string to search in
     * @param word string to be searched for
     * @return the answer to the question specified above
     */
    public static boolean containsWholeWord(String s, String word) {
        return Strings.containsWholeWord(s, word);
    }

    /**
     * There are different kinds of JML markers. See Section 4.4 "Annotation markers" of the JML
     * reference manual.
     *
     * @param comment
     * @return
     */
    public static boolean isJMLComment(String comment) {
        return Strings.isJMLComment(comment);
    }

    /**
     * <p>
     * Returns the display name of the applied rule in the given {@link Node} of the proof tree in
     * KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no
     *         one exists.
     */
    public static String getRuleDisplayName(Node node) {
        String name = null;
        if (node != null) {
            name = getRuleDisplayName(node.getAppliedRuleApp());
        }
        return name;
    }

    /**
     * <p>
     * Returns the display name of the {@link RuleApp}.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param ruleApp The given {@link RuleApp}.
     * @return The display name of the {@link RuleApp} or {@code null} if no one exists.
     */
    public static String getRuleDisplayName(RuleApp ruleApp) {
        String name = null;
        if (ruleApp != null) {
            Rule rule = ruleApp.rule();
            if (rule != null) {
                name = rule.displayName();
            }
        }
        return name;
    }

    /**
     * <p>
     * Returns the name of the applied rule in the given {@link Node} of the proof tree in KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no
     *         one exists.
     */
    public static String getRuleName(Node node) {
        String name = null;
        if (node != null) {
            name = getRuleName(node.getAppliedRuleApp());
        }
        return name;
    }

    /**
     * <p>
     * Returns the name of the {@link RuleApp}.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction, e.g. used in the Symbolic
     * Execution Tree Debugger.
     * </p>
     *
     * @param ruleApp The given {@link RuleApp}.
     * @return The display name of the {@link RuleApp} or {@code null} if no one exists.
     */
    public static String getRuleName(RuleApp ruleApp) {
        String name = null;
        if (ruleApp != null) {
            Rule rule = ruleApp.rule();
            if (rule != null) {
                name = rule.name().toString();
            }
        }
        return name;
    }

    /**
     * Returns the {@link OneStepSimplifier} used in the given {@link Proof}.
     *
     * @param proof The {@link Proof} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Proof proof) {
        if (proof != null && !proof.isDisposed() && proof.getInitConfig() != null) {
            Profile profile = proof.getInitConfig().getProfile();
            return findOneStepSimplifier(profile);
        } else {
            return null;
        }
    }

    /**
     * Returns the {@link OneStepSimplifier} used in the given {@link Profile}.
     *
     * @param profile The {@link Profile} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Profile profile) {
        if (profile instanceof JavaProfile) {
            return ((JavaProfile) profile).getOneStepSimpilifier();
        } else {
            return null;
        }
    }

    /**
     * Returns the actual variable for a given one (this means it returns the renamed variable).
     *
     * @param node the Node where to look up the actual variable (result from renaming)
     * @return The renamed variable
     */
    public static ProgramVariable findActualVariable(ProgramVariable originalVar, Node node) {
        ProgramVariable actualVar = originalVar;
        if (node != null) {
            outer: do {
                if (node.getRenamingTable() != null) {
                    for (RenamingTable rt : node.getRenamingTable()) {
                        ProgramVariable renamedVar = (ProgramVariable) rt.getRenaming(actualVar);
                        if (renamedVar != null || !node.getLocalProgVars().contains(actualVar)) {
                            actualVar = renamedVar;
                            break outer;
                        }
                    }
                }
                node = node.parent();
            } while (node != null);
        }
        return actualVar;
    }

    // -------------------------------------------------------------------------
    // inner classes
    // -------------------------------------------------------------------------

    private static final class ReadPVCollector extends JavaASTVisitor {
        /**
         * The list of resulting (i.e., read) program variables.
         */
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet.<ProgramVariable>nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable>nil();

        private final ProgramElement root;
        public ReadPVCollector(ProgramElement root, Services services) {
            super(root, services);
            this.root = root;
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof ProgramVariable) {
                ProgramVariable pv = (ProgramVariable) node;
                if (!pv.isMember() && !declaredPVs.contains(pv)) {
                    result = result.add(pv);
                }
            } else if (node instanceof AbstractPlaceholderStatement) {
                final AbstractPlaceholderStatement aps = (AbstractPlaceholderStatement) node;

                for (final ProgramVariable pv : AbstractExecutionContractUtils
                        .getAccessibleProgVarsForNoBehaviorContract(aps, root,
                                services)) {
                    if (!pv.isMember() && !declaredPVs.contains(pv)) {
                        result = result.add(pv);
                    }
                }
            } else if (node instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) node;
                ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                if (!pv.isMember()) {
                    assert !declaredPVs.contains(pv);
                    result = result.remove(pv);
                    declaredPVs = declaredPVs.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    private static class WrittenAndDeclaredPVCollector extends JavaASTVisitor {
        /**
         * The written program variables.
         */
        private ImmutableSet<ProgramVariable> writtenPVs =
                DefaultImmutableSet.<ProgramVariable>nil();

        /**
         * The declared program variables.
         */
        private ImmutableSet<ProgramVariable> declaredPVs =
                DefaultImmutableSet.<ProgramVariable>nil();

        private final ProgramElement root;
        public WrittenAndDeclaredPVCollector(ProgramElement root, Services services) {
            super(root, services);
            this.root = root;
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof Assignment) {
                ProgramElement lhs = ((Assignment) node).getChildAt(0);
                if (lhs instanceof ProgramVariable) {
                    ProgramVariable pv = (ProgramVariable) lhs;
                    if (!pv.isMember() && !declaredPVs.contains(pv)) {
                        writtenPVs = writtenPVs.add(pv);
                    }
                }
            } else if (node instanceof AbstractPlaceholderStatement) {
                final AbstractPlaceholderStatement aps = (AbstractPlaceholderStatement) node;

                for (final ProgramVariable pv : AbstractExecutionContractUtils
                        .getAssignableProgVarsForNoBehaviorContract(aps, root,
                                services)) {
                    if (!pv.isMember() && !declaredPVs.contains(pv)) {
                        writtenPVs = writtenPVs.add(pv);
                    }
                }
            } else if (node instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) node;
                ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                if (!pv.isMember()) {
                    assert !declaredPVs.contains(pv);
                    assert !writtenPVs.contains(pv);
                    declaredPVs = declaredPVs.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> getWrittenPVs() {
            return writtenPVs;
        }

        public ImmutableSet<ProgramVariable> getDeclaredPVs() {
            return declaredPVs;
        }
    }

    public static ImmutableList<Term> toTermList(Iterable<ProgramVariable> list,
            TermBuilder tb) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (ProgramVariable pv : list) {
            if (pv != null) {
                Term t = tb.var(pv);
                result = result.append(t);
            }
        }
        return result;
    }

    /**
     * read an input stream to its end into a string.
     *
     * @param is a non-null open input stream
     * @return the string created from the input of the stream
     * @throws IOException may occur while reading the stream
     */
    public static String toString(InputStream is) throws IOException {
        StringBuilder sb = new StringBuilder();
        byte[] buffer = new byte[2048];
        int read;
        while ((read = is.read(buffer)) > 0) {
            sb.append(new String(buffer, 0, read));
        }
        return sb.toString();
    }

    public static ImmutableList<Term> filterOutDuplicates(ImmutableList<Term> localIns,
            ImmutableList<Term> localOuts) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term localIn : localIns) {
            if (!localOuts.contains(localIn)) {
                result = result.append(localIn);
            }
        }
        return result;
    }

    /**
     * Returns the default taclet options.
     *
     * @return The default taclet options.
     */
    public static HashMap<String, String> getDefaultTacletOptions() {
        HashMap<String, String> result = new HashMap<String, String>();
        result.put("Strings", "Strings:on");
        result.put("reach", "reach:on");
        result.put("JavaCard", "JavaCard:off");
        result.put("assertions", "assertions:on");
        result.put("bigint", "bigint:on");
        result.put("intRules", "intRules:arithmeticSemanticsIgnoringOF");
        result.put("programRules", "programRules:Java");
        result.put("modelFields", "modelFields:showSatisfiability");
        result.put("initialisation", "initialisation:disableStaticInitialisation");
        result.put("sequences", "sequences:on");
        result.put("runtimeExceptions", "runtimeExceptions:allow");
        result.put("integerSimplificationRules", "integerSimplificationRules:full");
        result.put("optimisedSelectRules", "optimisedSelectRules:on");
        result.put("wdChecks", "wdChecks:off");
        result.put("wdOperator", "wdOperator:L");
        result.put("permissions", "permissions:off");
        return result;
    }

    /**
     * Returns the path to the source file defined by the given {@link PositionInfo}.
     *
     * @param posInfo The {@link PositionInfo} to extract source file from.
     * @return The source file name or {@code null} if not available.
     */
    public static String getSourcePath(PositionInfo posInfo) {
        String result = null;
        if (posInfo.getFileName() != null) {
            result = posInfo.getFileName(); // posInfo.getFileName() is a path to a file
        } else if (posInfo.getParentClass() != null) {
            result = posInfo.getParentClass(); // posInfo.getParentClass() is a path to a file
        }
        if (result != null && result.startsWith("FILE:")) {
            result = result.substring("FILE:".length());
        }
        return result;
    }

    /**
     * Dissects a term "x1 op x2 op ... op xn" to its constituents x1, ..., xn.
     * The result is a set, i.e., in case of double occurrences, later ones are
     * ignored. The result is sorted (LinkedHashSet):
     *
     * @param s
     *     The term to split.
     * @param splitAt
     *     The <strong>binary</strong> operation op at which to split.
     * @return The constituents of the given set-like term.
     */
    public static Set<Term> disasembleSetTerm(Term s, Function splitAt) {
        assert splitAt.arity() == 2;
        final Set<Term> result = new LinkedHashSet<Term>();

        if (s.op() == splitAt) {
            result.addAll(disasembleSetTerm(s.sub(0), splitAt));
            result.addAll(disasembleSetTerm(s.sub(1), splitAt));
        } else {
            result.add(s);
        }

        return result;
    }

    /**
     * Collects all {@link LocationVariable}s in the given {@link Term}, thereby
     * also considering {@link JavaBlock}s.
     *
     * @param t
     *     The {@link Term} from which to collect.
     * @param services
     *     The {@link Services} object, for the
     *     {@link ProgramVariableCollector}.
     *
     * @return All {@link LocationVariable}s in the given {@link Term}.
     */
    public static Set<LocationVariable> collectLocVars(final Term t,
            Services services) {
        final OpCollector opColl = new OpCollector();
        t.execPostOrder(opColl);
        final Set<LocationVariable> occurringLocVars = opColl.ops().stream()
                .filter(op -> op instanceof LocationVariable)
                .map(LocationVariable.class::cast).collect(Collectors.toSet());

        if (t.containsJavaBlockRecursive()) {
            final JavaBlock jb = MergeRuleUtils.getJavaBlockRecursive(t);
            final ProgramVariableCollector pvc = new ProgramVariableCollector(
                    jb.program(), services);
            pvc.start();
            occurringLocVars.addAll(pvc.result());
        }

        return occurringLocVars;
    }

    /**
     * Replaces all occurrences of pv by t in replaceIn.
     *
     * @param pv
     *     The {@link LocationVariable} to replace.
     * @param with
     *     The {@link Term} by which to replace pv.
     * @param replaceIn
     *     The {@link Term} in which to replace pv by t.
     * @param services
     *     The {@link Services} object, for the {@link TermBuilder}.
     * @return The {@link Term} replaceIn with all occurrences of pv replaced by
     * t.
     */
    public static Term replaceVarInTerm(LocationVariable pv, Term with,
            final Term replaceIn, Services services) {
        final Map<Term, Term> substMap = new HashMap<>();
        substMap.put(services.getTermBuilder().var(pv), with);
        final OpReplacer opRepl = new OpReplacer(substMap,
                services.getTermFactory());
        final Term newAbstrUpdLHS = opRepl.replace(replaceIn);
        return newAbstrUpdLHS;
    }

    /**
     * Simplifies, as much as safely possible, update / update applications
     * inside the given {@link Term}.
     *
     * @param t
     *     The {@link Term} in which to simplify updates.
     * @param services
     *     The {@link Services} object.
     * @return The simplified {@link Term}.
     */
    public static Term simplifyUpdatesInTerm(Term t, Services services) {
        if (t.op() instanceof ElementaryUpdate
                || t.op() == UpdateJunctor.PARALLEL_UPDATE) {
            t = simplifyUpdate(t, services);
        }

        return GenericTermReplacer.replace(t,
                term -> term.op() == UpdateApplication.UPDATE_APPLICATION,
                term -> simplifyUpdateApplication(term, services), services);
    }

    /**
     * Simplifies an update term (an empty, elementary, or parallel update):
     * Removes duplicates (later-one-wins rule) and applies update applications
     * in the right-hand sides, if possible. The result is a parallel update in
     * normal form (no duplicates, no nested update applications).
     *
     * @param t
     *     The update term to simplify.
     * @param services
     *     The {@link Services} object (for the {@link TermBuilder}).
     * @return The simplified update {@link Term}.
     */
    public static Term simplifyUpdate(Term t, Services services) {
        assert t.op() instanceof ElementaryUpdate
                || t.op() instanceof UpdateJunctor;
        if (t.op() == UpdateJunctor.SKIP) {
            return t;
        }

        final TermBuilder tb = services.getTermBuilder();
        // This already removes duplicates, later elems win
        final List<Term> elems = MergeRuleUtils.getElementaryUpdates(t,
                services.getTermBuilder());
        return tb.parallel(elems.stream()
                .map(elem -> tb.elementary(((ElementaryUpdate) elem.op()).lhs(),
                        simplifyUpdateApplication(elem.sub(0), services)))
                .collect(ImmutableSLList.toImmutableList()));
    }

    /**
     * This is a programmatic procedure to "execute" update applications, i.e.,
     * to apply in an update application term the update to the target. The
     * result will not contain update applications and is logically equivalent.
     * If the target contains a modality or update application, returns the
     * original term, because otherwise the method would either be unsound or we
     * would have to think way more for doing it correctly.
     *
     * @param t
     *     The update application term to simplify. If not an update application
     *     term, the original term is directly returned.
     * @param services
     *     The {@link Services} object.
     * @return The simplified term.
     */
    public static Term simplifyUpdateApplication(Term t, Services services) {
        if (t.op() != UpdateApplication.UPDATE_APPLICATION) {
            // We only apply update applications
            return t;
        }

        Term update = UpdateApplication.getUpdate(t);
        if (update.op() == UpdateApplication.UPDATE_APPLICATION) {
            // update not in normal form -- recursively simplify
            update = simplifyUpdateApplication(update, services);
        } else if (update.op() instanceof AbstractUpdate
                || update.op() == UpdateJunctor.CONCATENATED_UPDATE) {
            // Simplification of abstract updates is not what we do here
            return t;
        }

        final Term target = UpdateApplication.getTarget(t);

        if (target.containsJavaBlockRecursive()
                || containsUpdateApplications(target)) {
            /*
             * We don't apply the update if there's still a modal operator, way
             * more complicated then.
             */
            return t;
        }

        // This already removes duplicates, later elems win
        final List<Term> elems = MergeRuleUtils.getElementaryUpdates(
                simplifyUpdate(update, services), services.getTermBuilder());

        // Now apply the update to the target, step by step
        Term result = target;
        for (final Term elem : elems) {
            final LocationVariable lhs = //
                    (LocationVariable) ((ElementaryUpdate) elem.op()).lhs();
            result = replaceVarInTerm(lhs, elem.sub(0), result, services);
        }

        return result;
    }

    /**
     * @param t
     *     The Term to check.
     * @return true iff t contains an update application.
     */
    private static boolean containsUpdateApplications(Term t) {
        final FilterVisitor fv = new FilterVisitor(
                term -> term.op() == UpdateApplication.UPDATE_APPLICATION);
        t.execPostOrder(fv);
        return !fv.result().isEmpty();
    }

    /**
     * Abstract Execution added program variables to assignable terms. They
     * appear as "singletonPV(x)" terms in the modifies clause. For loop
     * invariant applications, they have to be ignored (we obtain the modified
     * visible locals by static analysis). Therefore, we filter them from the
     * modifies term by this method.
     *
     * @param modTerm
     *     The original modifies term, maybe with singletonPV functions.
     * @param services
     *     The {@link Services} object (for {@link TermBuilder} and
     *     {@link LocSetLDT}).
     * @return The modTerm without singletonPV subterms.
     */
    public static Term removeSingletonPVs(Term modTerm, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final TermBuilder tb = services.getTermBuilder();

        if (modTerm.op() == locSetLDT.getSingletonPV()) {
            return tb.empty();
        } else if (modTerm.op() == locSetLDT.getUnion()) {
            return tb.union(removeSingletonPVs(modTerm.sub(0), services),
                    removeSingletonPVs(modTerm.sub(1), services));
        } else {
            return modTerm;
        }
    }

    /**
     * Returns the {@link LoopSpecification} for the program in the given term,
     * the active statement of which has to be a loop statement. Returns an
     * empty {@link Optional} if there is no specification for that statement.
     * Asserts that there is indeed a Java block in the term which has as active
     * statement a loop statement, thus throws an {@link AssertionError} if not
     * or otherwise results in undefined behavior in that case.
     *
     * @param loopTerm
     *     The term for which to return the {@link LoopSpecification}.
     * @param services
     *     The {@link Services} object.
     *
     * @return The {@link LoopSpecification} for the loop statement in the given
     * term or an empty optional if there is no specified invariant for the
     * loop.
     */
    public static Optional<LoopSpecification>
            getSpecForTermWithLoopStmt(final Term loopTerm, Services services) {
        assert loopTerm.op() instanceof Modality;
        assert loopTerm.javaBlock() != JavaBlock.EMPTY_JAVABLOCK;

        final ProgramElement pe = loopTerm.javaBlock().program();
        assert pe != null;
        assert pe instanceof StatementBlock;
        assert ((StatementBlock) pe).getFirstElement() instanceof LoopStatement;

        final LoopStatement loop = //
                (LoopStatement) ((StatementBlock) pe).getFirstElement();

        return Optional.ofNullable(
                services.getSpecificationRepository().getLoopSpec(loop));
    }

    /**
     * @param services
     *     The {@link Services} object.
     * @return true iff the given {@link Services} object is associated to a
     * {@link Profile} with permissions.
     */
    public static boolean isPermissions(Services services) {
        return services.getProfile() instanceof JavaProfile
                && ((JavaProfile) services.getProfile()).withPermissions();
    }

    /**
     * Checks whether the given {@link Modality} is a transaction modality.
     *
     * @param modality
     *     The modality to check.
     * @return true iff the given {@link Modality} is a transaction modality.
     */
    public static boolean isTransaction(final Modality modality) {
        return modality == Modality.BOX_TRANSACTION
                || modality == Modality.DIA_TRANSACTION;
    }

    /**
     * Returns the applicable heap contexts out of the currently available set
     * of three contexts: The normal heap, the saved heap (transaction), and the
     * permission heap.
     *
     * @param modality
     *     The current modality (checked for transaction).
     * @param services
     *     The {@link Services} object (for {@link HeapLDT} and for checking
     *     whether we're in the permissions profile).
     * @return The list of the applicable heaps for the given scenario.
     */
    public static List<LocationVariable>
            applicableHeapContexts(Modality modality, Services services) {
        final List<LocationVariable> result = new ArrayList<>();

        result.add(services.getTypeConverter().getHeapLDT().getHeap());

        if (isTransaction(modality)) {
            result.add(services.getTypeConverter().getHeapLDT().getSavedHeap());
        }

        if (isPermissions(services)) {
            result.add(services.getTypeConverter().getHeapLDT()
                    .getPermissionHeap());
        }
        return result;
    }
}
