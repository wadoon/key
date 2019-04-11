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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

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
 * Collection of some common, stateless functionality. Stolen from
 * the weissInvariants side branch.
 */
public final class MiscTools {


    private MiscTools() {}


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------


    // TODO Is rp always a program variable?
    public static ProgramVariable getSelf(MethodFrame mf) {
        ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
        ReferencePrefix rp = ec.getRuntimeInstance();
        if(!(rp instanceof TypeReference) && rp != null) {
            return (ProgramVariable) rp;
        } else {
            return null;
        }
    }


    /**
     * Returns the receiver term of the passed method frame, or null if
     * the frame belongs to a static method.
     */
    public static Term getSelfTerm(MethodFrame mf, Services services) {
	ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
	ReferencePrefix rp = ec.getRuntimeInstance();
	if(!(rp instanceof TypeReference) && rp != null) {
	    return services.getTypeConverter().convertToLogicElement(rp);
	} else {
	    return null;
	}
    }

    public static ImmutableSet<ProgramVariable> getLocalIns(ProgramElement pe,
	    					     	    Services services) {
	final ReadPVCollector rpvc = new ReadPVCollector(pe, services);
	rpvc.start();
	return rpvc.result();
    }


    public static ImmutableSet<ProgramVariable> getLocalOuts(
	    					ProgramElement pe,
	    			                Services services) {
	final WrittenPVCollector wpvc = new WrittenPVCollector(pe, services);
	wpvc.start();
	return wpvc.result();
    }


    public static ImmutableSet<Pair<Sort,IObserverFunction>>
    						collectObservers(Term t) {
	ImmutableSet<Pair<Sort, IObserverFunction>> result
		= DefaultImmutableSet.nil();
	if(t.op() instanceof IObserverFunction) {
	    final IObserverFunction obs = (IObserverFunction)t.op();
	    final Sort s = obs.isStatic()
	             	   ? obs.getContainerType().getSort()
	                   : t.sub(1).sort();
	    result = result.add(new Pair<Sort,IObserverFunction>(s, obs));
	}
	for(Term sub : t.subs()) {
	    result = result.union(collectObservers(sub));
	}
	return result;
    }

    /**
     * True if both are <code>null</code> or <code>a.equals(b)</code> with <code>equals</code> from type T.
     */
    public static <T> boolean equalsOrNull(T a, Object b){
        if (a == null) {
            return b == null;
        } else {
            return a.equals(b);
        }
    }

    public static <T> boolean equalsOrNull(T a, Object... bs){
        boolean result = true;
        for (Object b: bs){
            result = result && equalsOrNull(a, b);
        }
        return result;
    }


    // =======================================================
    // Methods operating on Arrays
    // =======================================================
    
    /**
     * Concatenates two arrays.
     * The second array may have an entry type that is a
     * subtype of the first one.
     */
    public static <S,T extends S> S[] concat(S[] s1, T[] s2) {
        S[] res = Arrays.copyOf(s1, s1.length+s2.length);
        for (int i= 0; i < s2.length; i++)
            res[i+s1.length] = s2[i];
        return res;
    }


    // =======================================================
    // Methods operating on Collections
    // =======================================================

    /** Combine two maps by function application.
     * Values of <code>m0</code> which are not keys of <code>m1</code>
     * are dropped.
     * This implementation tries to use the same implementation of {@link java.util.Map}
     * (provided in Java SE) as <code>m0</code>.
     */
    public static <S,T,U> Map<S,U> apply(Map<S,? extends T> m0, Map<T,U> m1) {
        Map<S,U> res = null;
        final int size = m0.size() < m1.size()? m0.size(): m1.size();
        // try to use more specific implementation
        if (m0 instanceof java.util.TreeMap)
            res = new java.util.TreeMap<S,U>();
        else if (m0 instanceof java.util.concurrent.ConcurrentHashMap)
            res = new java.util.concurrent.ConcurrentHashMap<S,U>(size);
        else if (m0 instanceof java.util.IdentityHashMap)
            res = new java.util.IdentityHashMap<S, U>(size);
        else if (m0 instanceof java.util.WeakHashMap)
            res = new java.util.WeakHashMap<S,U>(size);
        else res = new HashMap<S,U>(size);

        for (Entry<S, ? extends T> e: m0.entrySet()) {
            final U value = m1.get(e.getValue());
            if (value != null)
                res.put(e.getKey(), value);
        }
        return res;
    }


    // =======================================================
    // Methods operating on Strings
    // =======================================================

    /**
     * Separates the single directory entries in a filename.
     * The first element is an empty String iff the filename is absolute.
     * (For a Windows filename, it contains a drive letter and a colon).
     * Ignores double slashes and slashes at the end, removes references to the cwd.
     * E.g., "/home//daniel/./key/" yields {"","home","daniel","key"}.
     * Tries to automatically detect UNIX or Windows directory delimiters.
     * There is no check whether all other characters are valid for filenames.
     */
    static List<String> disectFilename(String filename){
        final char sep = File.separatorChar;
        List<String> res = new ArrayList<String>();
        // if filename contains slashes, take it as UNIX filename, otherwise Windows
        if (filename.indexOf("/") != -1) assert sep == '/' : "\""+filename+"\" contains both / and \\";
        else if (filename.indexOf("\\") != -1) assert sep == '\\': "\""+filename+"\" contains both / and \\";
        else {
            res.add(filename);
            return res;
        }
        int i = 0;
        while (i < filename.length()){
            int j = filename.indexOf(sep,i);
            if (j == -1){ // no slash anymore
                final String s = filename.substring(i, filename.length());
                if (!s.equals("."))
                    res.add(s);
                break;
            }
            if (i == j) {
                // empty string between slashes
                if (i == 0)
                    // leading slash
                    res.add("");
            } else {
                // contains "/./"
                final String s = filename.substring(i, j);
                if (!s.equals(".")) {
                    res.add(s);
                }
            }
            i = j+1;
        }
        return res;
    }

    /** Returns a filename relative to another one.
     * The second parameter needs to be absolute and is expected to refer to directory
     * This method only operates on Strings, not on real files!
     * Note that it treats Strings case-sensitive.
     * The resulting filename always uses UNIX directory delimiters.
     * Raises a RuntimeException if no relative path could be found
     * (may happen on Windows systems).
     */
    public static String makeFilenameRelative(String origFilename, String toFilename){
        final List<String> origFileNameSections = disectFilename(origFilename);
        String[] a = origFileNameSections.toArray(new String[origFileNameSections.size()]);
        final List<String> destinationFilenameSections = disectFilename(toFilename);
        String[] b = destinationFilenameSections.toArray(new String[destinationFilenameSections.size()]);

        // check for Windows paths
        if (File.separatorChar == '\\' &&
                a[0].length() == 2 && a[0].charAt(1) == ':') {
            char drive = Character.toUpperCase(a[0].charAt(0));
            if (!(b[0].length() == 2 && Character.toUpperCase(b[0].charAt(0)) == drive && b[0].charAt(1) == ':'))
                throw new RuntimeException("cannot make paths on different drives relative");
            // remove drive letter
            a[0] = ""; b[0] = "";
        }
        int i;
        String s = "";
        String t = "";

        if (a[0].equals("")) { // not already relative
        if (!b[0].equals(""))
            throw new RuntimeException("\""+toFilename+ "\" is a relative path. Please use absolute paths to make others relative to them.");

        // remove ".." from paths
        a = removeDotDot(a);
        b = removeDotDot(b);

        // FIXME: there may be leading ..'s

        i = 1; boolean diff= false;
        while (i < b.length){
            // shared until i
            if (i >= a.length || !a[i].equals(b[i])) diff = true;
            // add ".." for each remaining element in b
            // and collect the remaining elements of a
            if (diff) {
                s = s + "../";
                if (i < a.length)
                    t = t + (a[i].equals("")? "" : "/")+ a[i];
            }
            i++;
        }
        } else { i = 0; }
        while (i < a.length)
            t = t +(a[i].equals("")? "" : "/")+ a[i++];
        // strip leading slash
        if (t.length()>0 && t.charAt(0) == '/')
            t = t.substring(1);
        // strip ending slash
        t = s + t;
        if (t.length() > 0 && t.charAt(t.length()-1) == '/')
            t = t.substring(0,t.length()-1);
        return t;
    }


    private static String[] removeDotDot(String[] a) {
        String[] newa = new String[a.length];
        int k = 0;
        for (int j = 0; j < a.length-1; j++){
            if (a[j].equals("..") || !a[j+1].equals("..")){
                newa[k++] = a[j];
            } else
                j++;
        }
        if (!a[a.length-1].equals("..")){
            newa[k++] = a[a.length-1];
        }
        return Arrays.copyOf(newa, k);
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
     * Join the string representations of a collection of objects into onw
     * string. The individual elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection
     *            an arbitrary non-null collection
     * @param delimiter
     *            a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the
     *         delimiter
     */
    public static String join(Iterable<?> collection, String delimiter) {
        StringBuilder sb = new StringBuilder();
        for (Object obj : collection) {
            if(sb.length() > 0) {
                sb.append(delimiter);
            }
            sb.append(obj);
        }

        return sb.toString();
    }

    /**
     * Join the string representations of an array of objects into one
     * string. The individual elements are separated by a delimiter.
     *
     * {@link Object#toString()} is used to turn the objects into strings.
     *
     * @param collection
     *            an arbitrary non-null array of objects
     * @param delimiter
     *            a non-null string which is put between the elements.
     *
     * @return the concatenation of all string representations separated by the
     *         delimiter
     */
    public static String join(Object[] collection, String delimiter) {
        return join(Arrays.asList(collection), delimiter);
    }

    /**
     * Takes a string and returns a string which is potentially shorter and
     * contains a sub-collection of the original characters.
     *
     * All alphabetic characters (A-Z and a-z) are copied to the result while
     * all other characters are removed.
     *
     * @param string
     *            an arbitrary string
     * @return a string which is a sub-structure of the original character
     *         sequence
     *
     * @author mattias ulbrich
     */
    public static /*@ non_null @*/ String filterAlphabetic(/*@ non_null @*/ String string) {
        StringBuilder res = new StringBuilder();
        for (int i = 0; i < string.length(); i++) {
            char c = string.charAt(i);
            if((c >= 'A' && c <= 'Z') || (c >= 'A' && c <= 'Z')) {
                res.append(c);
            }
        }
        return res.toString();
    }

    /** Checks whether a string contains another one as a whole word
     * (i.e., separated by whitespaces or a semicolon at the end).
     * @param s string to search in
     * @param word string to be searched for
     */
    public static boolean containsWholeWord(String s, String word){
        if (s == null || word == null) return false;
        int i = -1;
        final int wl = word.length();
        while (true) {
            i = s.indexOf(word, i+1);
            if (i < 0 || i >= s.length()) break;
            if (i == 0 || Character.isWhitespace(s.charAt(i-1))) {
                if (i+wl == s.length() || Character.isWhitespace(s.charAt(i+wl)) || s.charAt(i+wl) == ';') {
                    return true;
                }
            }
        }
        return false;
    }


    /** There are different kinds of JML markers.
     * See Section 4.4 "Annotation markers" of the JML reference manual.
     * @param comment
     * @return
     */
    public static boolean isJMLComment(String comment) {
        try {
        return (comment.startsWith("/*@") || comment.startsWith("//@")
                || comment.startsWith("/*+KeY@") || comment.startsWith("//+KeY@")
                || (comment.startsWith("/*-")&& !comment.substring(3,6).equals("KeY") && comment.contains("@"))
                || (comment.startsWith("//-") && !comment.substring(3,6).equals("KeY") && comment.contains("@")));
        } catch (IndexOutOfBoundsException e){
            return false;
        }
    }

    /**
     * <p>
     * Returns the display name of the applied rule in the given {@link Node} of
     * the proof tree in KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no one exists.
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
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
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
     * Returns the name of the applied rule in the given {@link Node} of
     * the proof tree in KeY.
     * </p>
     * <p>
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no one exists.
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
     * This method is required for the symbolic execution tree extraction,
     * e.g. used in the Symbolic Execution Tree Debugger.
     * </p>
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
     * @param proof The {@link Proof} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Proof proof) {
       if (proof != null && !proof.isDisposed() && proof.getInitConfig() !=null) {
          Profile profile = proof.getInitConfig().getProfile();
          return findOneStepSimplifier(profile);
       }
       else {
          return null;
       }
    }
    
    /**
     * Returns the {@link OneStepSimplifier} used in the given {@link Profile}.
     * @param profile The {@link Profile} to get its used {@link OneStepSimplifier}.
     * @return The used {@link OneStepSimplifier} or {@code null} if not available.
     */
    public static OneStepSimplifier findOneStepSimplifier(Profile profile) {
       if (profile instanceof JavaProfile) {
          return ((JavaProfile) profile).getOneStepSimpilifier();
       }
       else {
          return null;
       }
    }

    /**
     * Returns the actual variable for a given one (this means it returns the renamed variable).
     * @param node the Node where to look up the actual variable (result from renaming)
     * @return The renamed variable
     */
    public static ProgramVariable findActualVariable(ProgramVariable originalVar, Node node) {
        ProgramVariable actualVar = originalVar;
        if (node != null) {          
            outer:
                do {
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

    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------

    private static final class ReadPVCollector extends JavaASTVisitor {
	private ImmutableSet<ProgramVariable> result
		= DefaultImmutableSet.<ProgramVariable>nil();

        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable> nil();

        private final ProgramElement root;

	public ReadPVCollector(ProgramElement root, Services services) {
	    super(root, services);
            this.root = root;
	}

	@Override
	protected void doDefaultAction(SourceElement node) {
	    if(node instanceof ProgramVariable) {
		ProgramVariable pv = (ProgramVariable) node;
		if(!pv.isMember() && !declaredPVs.contains(pv)) {
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
	    } else if(node instanceof VariableSpecification) {
		VariableSpecification vs = (VariableSpecification) node;
		ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
		if(!pv.isMember()) {
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


    private static final class WrittenPVCollector extends JavaASTVisitor {
	private ImmutableSet<ProgramVariable> result
		= DefaultImmutableSet.<ProgramVariable>nil();

	private ImmutableSet<ProgramVariable> declaredPVs
		= DefaultImmutableSet.<ProgramVariable>nil();

        private final ProgramElement root;

	public WrittenPVCollector(ProgramElement root, Services services) {
	    super(root, services);
            this.root = root;
	}

	@Override
	protected void doDefaultAction(SourceElement node) {
	    if(node instanceof Assignment) {
		ProgramElement lhs = ((Assignment) node).getChildAt(0);
		if(lhs instanceof ProgramVariable) {
		    ProgramVariable pv = (ProgramVariable) lhs;
		    if(!pv.isMember() && !declaredPVs.contains(pv)) {
			result = result.add(pv);
		    }
		}
            } else if (node instanceof AbstractPlaceholderStatement) {
                final AbstractPlaceholderStatement aps = (AbstractPlaceholderStatement) node;

                for (final ProgramVariable pv : AbstractExecutionContractUtils
                        .getAssignableProgVarsForNoBehaviorContract(aps, root,
                                services)) {
                    if (!pv.isMember() && !declaredPVs.contains(pv)) {
                        result = result.add(pv);
                    }
                }
	    } else if(node instanceof VariableSpecification) {
		VariableSpecification vs = (VariableSpecification) node;
		ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
		if(!pv.isMember()) {
		    assert !declaredPVs.contains(pv);
		    assert !result.contains(pv);
		    declaredPVs = declaredPVs.add(pv);
		}
	    }
	}

	public ImmutableSet<ProgramVariable> result() {
	    return result;
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
     * @param is
     *            a non-null open input stream
     * @return the string created from the input of the stream
     * @throws IOException may occur while reading the stream
     */
    public static String toString(InputStream is) throws IOException {
        StringBuilder sb = new StringBuilder();
        byte[] buffer = new byte[2048];
        int read;
        while((read=is.read(buffer)) > 0) {
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
     * @param posInfo The {@link PositionInfo} to extract source file from.
     * @return The source file name or {@code null} if not available.
     */
    public static String getSourcePath(PositionInfo posInfo) {
       String result = null;
       if (posInfo.getFileName() != null) {
          result = posInfo.getFileName(); // posInfo.getFileName() is a path to a file
       }
       else if (posInfo.getParentClass() != null) {
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
     *            The term to split.
     * @param splitAt
     *            The <strong>binary</strong> operation op at which to split.
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
     *            The {@link Term} from which to collect.
     * @param services
     *            The {@link Services} object, for the
     *            {@link ProgramVariableCollector}.
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
     *            The {@link LocationVariable} to replace.
     * @param with
     *            The {@link Term} by which to replace pv.
     * @param replaceIn
     *            The {@link Term} in which to replace pv by t.
     * @param services
     *            The {@link Services} object, for the {@link TermBuilder}.
     * @return The {@link Term} replaceIn with all occurrences of pv replaced by
     *         t.
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
     *            The {@link Term} in which to simplify updates.
     * @param services
     *            The {@link Services} object.
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
     *            The update term to simplify.
     * @param services
     *            The {@link Services} object (for the {@link TermBuilder}).
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
     *            The update application term to simplify. If not an update
     *            application term, the original term is directly returned.
     * @param services
     *            The {@link Services} object.
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
     *            The Term to check.
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
     *            The original modifies term, maybe with singletonPV functions.
     * @param services
     *            The {@link Services} object (for {@link TermBuilder} and
     *            {@link LocSetLDT}).
     * @return The modTerm without singletonPV subterms.
     */
    public static Term removeSingletonPVs(Term modTerm, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final TermBuilder tb = services.getTermBuilder();
    
        if (modTerm.op() == locSetLDT.getSingletonPV()) {
            return tb.empty();
        }
        else if (modTerm.op() == locSetLDT.getUnion()) {
            return tb.union(removeSingletonPVs(modTerm.sub(0), services),
                    removeSingletonPVs(modTerm.sub(1), services));
        }
        else {
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
     *            The term for which to return the {@link LoopSpecification}.
     * @param services
     *            The {@link Services} object.
     * 
     * @return The {@link LoopSpecification} for the loop statement in the given
     *         term or an empty optional if there is no specified invariant for
     *         the loop.
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
     *            The {@link Services} object.
     * @return true iff the given {@link Services} object is associated to a
     *         {@link Profile} with permissions.
     */
    public static boolean isPermissions(Services services) {
        return services.getProfile() instanceof JavaProfile
                && ((JavaProfile) services.getProfile()).withPermissions();
    }


    /**
     * Checks whether the given {@link Modality} is a transaction modality.
     * 
     * @param modality
     *            The modality to check.
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
     *            The current modality (checked for transaction).
     * @param services
     *            The {@link Services} object (for {@link HeapLDT} and for
     *            checking whether we're in the permissions profile).
     * @return The list of the applicable heaps for the given scenario.
     */
    public static List<LocationVariable> applicableHeapContexts(Modality modality,
            Services services) {
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
