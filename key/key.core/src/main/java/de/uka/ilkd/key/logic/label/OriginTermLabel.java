package de.uka.ilkd.key.logic.label;

import java.io.File;
import java.net.URI;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.label.OriginTermLabelRefactoring;
import de.uka.ilkd.key.util.Debug;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.service.KeYCrossReferenceSourceInfo;

/**
 * <p> An {@link OriginTermLabel} saves a term's origin(s) in the JML specification
 * ({@link #getOrigins()}). </p>
 * 
 * <p> For terms which have a single well-defined origin (e.g., a contract clause),
 * the set returned by {@link #getOrigins()} has size 1 and contains exactly that
 * origin.
 * For terms whose subterms have different origins,
 * the set returned by {@link #getOrigins()} has size {@code > 1} and contains all
 * origins of all subterms.
 *
 * <p> For this to work correctly, you must call
 * {@link #collectSubtermOrigins(Term, TermBuilder)} for every top-level formula in your
 * original proof obligation.
 * Before doing this, you can call {@link TermBuilder#addLabelToAllSubs(Term, TermLabel)}
 * for every term you have added to the original contract in your PO to add an
 * {@link OriginTermLabel}
 * of your choosing. Terms for which you do not do this get a label of the form
 * {@code new OriginTermLabel(Collections.emptySet())}. </p>
 *
 * @author lanzinger
 */
public class OriginTermLabel implements TermLabel {
    public static final Logger LOGGER = LoggerFactory.getLogger(OriginTermLabel.class);

    /**
     * Display name for {@link OriginTermLabel}s.
     */
    public final static Name NAME = new Name("origin");

    /**
     * @see #getChildCount()
     */
    public final static int CHILD_COUNT = 1;


    /**
     * Find a term's origins.
     * If the term has no origin, iterate through its parent terms until we find one with an origin.
     *
     * @param pis the position of the term whose origin to find.
     * @return the term's origins, or the origins of one of its parents.
     */
    public static Set<Origin> getOrigins(PosInSequent pis) {
        if (pis == null) {
            return null;
        }

        return getOrigins(pis.getPosInOccurrence());
    }

    /**
     * Find a term's origins.
     * If the term has no origin, iterate through its parent terms until we find one with an origin.
     *
     * @param pio the position of the term whose origin to find.
     * @return the term's origins, or the origins of one of its parents.
     */
    public static Set<Origin> getOrigins(PosInOccurrence pio) {
        if (pio == null) {
            return null;
        }

        Term term = pio.subTerm();

        OriginTermLabel originLabel =
                (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);
        
        if (originLabel != null) {
            return originLabel.getOrigins();
        }

        // If the term has no origin,
        // iterate over its parent terms until we find one with some origins.
        // But only return that origin if it is unique, otherwise we get a set of possibly
        // unrelated origins of the term's siblings.
        while (!pio.isTopLevel()) {
            pio = pio.up();
            term = pio.subTerm();
            
            originLabel =
                    (OriginTermLabel) term.getLabel(OriginTermLabel.NAME);

            if (originLabel != null) {
                if (originLabel.getOrigins().size() == 1) {
                    return originLabel.getOrigins();
                } else {
                    return Collections.emptySet();
                }
            }
        }
        
        return Collections.emptySet();
    }

    /**
     * This term's origins.
     * @see #getOrigins()
     */
    private final Set<Origin> origins;

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param origin the term's single origin.
     */
    public OriginTermLabel(Origin origin) {
        this.origins = Set.of(origin);
    }

    /**
     * Creates a new {@link OriginTermLabel}.
     *
     * @param origins the term's origins.
     */
    public OriginTermLabel(Set<Origin> origins) {
        assert !origins.isEmpty();
        
        this.origins = new LinkedHashSet<>();
        this.origins.addAll(origins);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((origins == null) ? 0 : origins.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof OriginTermLabel) {
            OriginTermLabel other = (OriginTermLabel) obj;
            return other.origins.equals(origins);
        } else {
            return false;
        }
    }

    /**
     * <p> Determines whether an {@code OriginTermLabel} can be added to the specified term. </p>
     *
     * <p> E.g., no labels should be added to terms whose operator is a heap variable as this leads
     * to various problems during proof search. </p>
     *
     * @param term a term
     * @param services services.
     * @return {@code true} iff an {@code OriginTermLabel} can be added to the specified term.
     */
    public static boolean canAddLabel(Term term, Services services) {
        return term != null && canAddLabel(term.op(), services);
    }

    /**
     * <p> Determines whether an {@code OriginTermLabel} can be added to a term with the specified
     * operator. </p>
     *
     * <p> E.g., no labels should be added to terms whose operator is a heap variable as this leads
     * to various problems during proof search. </p>
     *
     * @param op the specified operator.
     * @param services services.
     * @return {@code true} iff an {@code OriginTermLabel} can be added to a term
     *  with the specified operator.
     */
    public static boolean canAddLabel(Operator op, Services services) {
        //TODO: Instead of not adding origin labels to certain terms, we should investigate why
        // adding labels to these kinds of terms breaks the prover and fix these issues.

        final TypeConverter tc = services.getTypeConverter();
        final JavaInfo ji = services.getJavaInfo();

        if (op.arity() == 0) {
            Sort sort = op.sort(new ImmutableArray<>());

            if (sort.extendsTrans(Sort.FORMULA)) {
                return true;
            } else if (op instanceof ProgramVariable) {
                return !sort.extendsTrans(tc.getHeapLDT().targetSort())
                        && !sort.extendsTrans(tc.getLocSetLDT().targetSort())
                        //&& !op.name().equals(ji.getInv().name())
                        && !op.name().toString().endsWith(SpecificationRepository.LIMIT_SUFFIX);
            } else {
                return false;
            }
        } else {
            return !(op instanceof Function)
                    || (op.getClass().equals(Function.class)
                            && ((Function) op).sort().extendsTrans(Sort.FORMULA));
        }
    }

    /**
     * Removes all {@link OriginTermLabel}s from the specified sequent.
     *
     * @param seq the sequent to transform.
     * @param services services.
     * @return the resulting sequent change info.
     */
    public static SequentChangeInfo removeOriginLabels(Sequent seq, Services services) {
        SequentChangeInfo changes = null;

        for (int i = 1; i <= seq.size(); ++i) {
            SequentFormula oldFormula = seq.getFormulabyNr(i);
            SequentFormula newFormula = new SequentFormula(
                    OriginTermLabel.removeOriginLabels(oldFormula.formula(), services));
            SequentChangeInfo change = seq.changeFormula(
                    newFormula,
                    PosInOccurrence.findInSequent(seq, i, PosInTerm.getTopLevel()));

            if (changes == null) {
                changes = change;
            } else {
                changes.combine(change);
            }
        }

        return changes;
    }

    /**
     * Removes all {@link OriginTermLabel} from the specified term and its sub-terms.
     *
     * @param term the term to transform.
     * @param services services.
     * @return the transformed term.
     */
    public static Term removeOriginLabels(Term term, Services services) {
        if (term == null) {
            return null;
        }

        List<TermLabel> labels = term.getLabels().toList();
        final TermLabel originTermLabel = term.getLabel(NAME);
        final TermFactory tf = services.getTermFactory();
        final ImmutableArray<Term> oldSubs = term.subs();
        Term[] newSubs = new Term[oldSubs.size()];

        if (originTermLabel != null) {
            labels.remove(originTermLabel);
        }

        for (int i = 0; i < newSubs.length; ++i) {
            newSubs[i] = removeOriginLabels(oldSubs.get(i), services);
        }

        return tf.createTerm(term.op(),
                             newSubs,
                             term.boundVars(),
                             term.javaBlock(),
                             new ImmutableArray<>(labels));
    }

    /**
     * Iterates through all subterms to collect their origins,
     * then adds an origin label to the top-level term containing
     * all collected origins.
     *
     * @param term the term to transform.
     * @param services services.
     * @return the transformed term.
     */
    public static Term collectSubtermOrigins(Term term, Services services) {
        if (!canAddLabel(term, services)) {
            return term;
        }
        
        ImmutableArray<Term> subs = term.subs();
        Term[] newSubs = new Term[subs.size()];
        Set<Origin> origins = new LinkedHashSet<>();

        for (int i = 0; i < newSubs.length; ++i) {
            newSubs[i] = collectSubtermOrigins(subs.get(i), services);
            final OriginTermLabel subLabel = (OriginTermLabel) newSubs[i].getLabel(NAME);

            if (subLabel != null) {
                origins.addAll(subLabel.getOrigins());
            }
        }
        
        List<TermLabel> labels = term.getLabels().toList();
        final OriginTermLabel oldLabel = (OriginTermLabel) term.getLabel(NAME);
        if (oldLabel != null) {
            labels.remove(oldLabel);
            origins.addAll(oldLabel.getOrigins());
        }
        if (!origins.isEmpty()) {
            labels.add(new OriginTermLabel(origins));
        }

        return services.getTermFactory().createTerm(term.op(),
                                                    new ImmutableArray<>(newSubs),
                                                    term.boundVars(),
                                                    term.javaBlock(),
                                                    new ImmutableArray<>(labels));
    }

    @Override
    public String toString() {
        return "" + NAME + "(" + origins + ")";
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        if (i == 0) {
            return origins;
        } else {
            throw new IllegalArgumentException("OriginTermLabel has 1 child, but child index " + i + " was given.");
        }
    }

    @Override
    public int getChildCount() {
        return CHILD_COUNT;
    }

    @Override
    public boolean isProofRelevant() {
        return false;
    }

    /**
     *
     * @return the term's origins.
     */
    public Set<Origin> getOrigins() {
        return Collections.unmodifiableSet(origins);
    }

    /**
     * An origin encapsulates some information about where a term originates from.
     *
     * @author lanzinger
     */
    public static class Origin implements Comparable<Origin> {
        /**
         * The spec type the term originates from.
         */
        public final SpecType specType;

        /**
         * Creates a new {@link OriginTermLabel.Origin}.
         *
         * @param specType the spec type the term originates from.
         */
        public Origin(SpecType specType) {
            assert specType != null;

            this.specType = specType;
        }


        @Override
        public int compareTo(Origin other) {
            return Integer.compare(hashCode(), other.hashCode());
        }

        @Override
        public boolean equals(Object obj) {
            return obj != null
                    && obj.getClass().equals(getClass()) && ((Origin) obj).specType == specType;
        }

        @Override
        public int hashCode() {
            return specType.hashCode();
        }

        @Override
        public String toString() {
            return specType + " (implicit)";
        }
    }

    /**
     * Origin for terms that originate from a proof node.
     *
     * @author lanzinger
     */
    public static final class NodeOrigin extends Origin {

        /**
         * The name of the rule applied at the node the term originates from.
         */
        public final String ruleName;

        /**
         * The {@link Node#serialNr()} of the node the term originates from.
         */
        public final int nodeNr;

        /**
         * Creates a new {@link OriginTermLabel.Origin}.
         *
         * @param specType the spec type the term originates from.
         * @param ruleName the name of the rule applied at the node the term originates from.
         * @param nodeNr the {@link Node#serialNr()} of the node the term originates from.
         */
        public NodeOrigin(SpecType specType, String ruleName, int nodeNr) {
            super(specType);

            assert ruleName != null;

            this.ruleName = ruleName;
            this.nodeNr = nodeNr;
        }

        @Override
        public String toString() {
            return specType + " @ node " + nodeNr + " (" + ruleName + ")";
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!super.equals(obj)) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            NodeOrigin other = (NodeOrigin) obj;
            if (nodeNr != other.nodeNr) {
                return false;
            }
            if (ruleName == null) {
                if (other.ruleName != null) {
                    return false;
                }
            } else if (!ruleName.equals(other.ruleName)) {
                return false;
            }
            return true;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = super.hashCode();
            result = prime * result + nodeNr;
            result = prime * result + ((ruleName == null) ? 0 : ruleName.hashCode());
            return result;
        }
    }

    /**
     * Origin for terms that originate from a file.
     *
     * @author lanzinger
     */
    public static final class FileOrigin extends Origin {

        /**
         * The file the term originates from.
         */
        public final URI fileName;

        /**
         * The line in the file the term originates from.
         */
        public final int line;

        /**
         * Creates a new {@link OriginTermLabel.Origin}.
         *
         * @param specType the spec type the term originates from.
         * @param fileName the file the term originates from.
         * @param line the line in the file.
         */
        public FileOrigin(SpecType specType, String fileName, int line) {
            super(specType);

            assert fileName != null;
            assert line >= 0;

            // wrap fileName into URI
            // bugfix #1622: do not interpret "<unknown>" as file name
            if (fileName.equals("no file") || fileName.equals("<unknown>")) {
                this.fileName = null;
            } else {
                this.fileName = new File(fileName).toURI();
            }
            this.line = line;
        }

        @Override
        public String toString() {
            if (fileName == null) {
                return specType + " @ [no file]";
            } else {
                return specType + " @ file " + new File(fileName).getName() + " @ line " + line;
            }
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = super.hashCode();
            result = prime * result + ((fileName == null) ? 0 : fileName.hashCode());
            result = prime * result + line;
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (!super.equals(obj)) {
                return false;
            }
            if (getClass() != obj.getClass()) {
                return false;
            }
            FileOrigin other = (FileOrigin) obj;
            if (fileName == null) {
                if (other.fileName != null) {
                    return false;
                }
            } else if (!fileName.equals(other.fileName)) {
                return false;
            }
            if (line != other.line) {
                return false;
            }
            return true;
        }
    }

    /**
     * A {@code SpecType} is any type of JML specification which gets translated into JavaDL.
     *
     * @author lanzinger
     * @see OriginTermLabel.Origin
     */
    public static enum SpecType {

        /**
         * accessible
         */
        ACCESSIBLE("accessible"),

        /**
         * assert
         */
        ASSERT("assert"),

        /**
         * assignable
         */
        ASSIGNABLE("assignable"),

        /**
         * assume
         */
        ASSUME("assume"),

        /**
         * decreases
         */
        DECREASES("decreases"),

        /**
         * measured_by
         */
        MEASURED_BY("measured_by"),

        /**
         * invariant
         */
        INVARIANT("invariant"),

        /**
         * loop_invariant
         */
        LOOP_INVARIANT("loop_invariant"),

        /**
         * loop_invariant_free
         */
        LOOP_INVARIANT_FREE("loop_invariant_free"),

        /**
         * requires
         */
        REQUIRES("requires"),

        /**
         * requires_free
         */
        REQUIRES_FREE("requires_free"),

        /**
         * ensures
         */
        ENSURES("ensures"),

        /**
         * ensures_free
         */
        ENSURES_FREE("ensures_free"),

        /**
         * signals
         */
        SIGNALS("signals"),

        /**
         * signals_only
         */
        SIGNALS_ONLY("signals_only"),

        /**
         * breaks
         */
        BREAKS("breaks"),

        /**
         * continues
         */
        CONTINUES("continues"),

        /**
         * returns
         */
        RETURNS("returns"),

        /**
         * Interaction. Used for terms entered by the user.
         */
        USER_INTERACTION("User_Interaction"),
        
        /**
         * Unknown. Used for terms whose origin was not specified
         * upon their creation.
         */
        UNKNOWN("Unknown");

        /**
         * This {@code SpecType}'s string representation.
         */
        private String name;

        /**
         * Creates a new {@code SpecType}
         *
         * @param name the {@code SpecType}'s string representation.
         */
        private SpecType(String name) {
            this.name = name;
        }

        @Override
        public String toString() {
            return name;
        }
    }
}
