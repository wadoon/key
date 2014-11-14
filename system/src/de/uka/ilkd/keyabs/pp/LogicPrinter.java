// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.keyabs.pp;

import java.io.IOException;
import java.io.StringWriter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.ILogicPrinter;
import de.uka.ilkd.key.pp.INotationInfo;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.ModalityPositionTable;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentPrintFilterEntry;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NewDependingOn;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.NotFreeIn;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.pp.Backend;
import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;
import de.uka.ilkd.keyabs.abs.*;
import de.uka.ilkd.keyabs.abs.ABSReturnStatement;
import de.uka.ilkd.keyabs.abs.expression.ABSBinaryOperatorPureExp;
import de.uka.ilkd.keyabs.abs.expression.ABSDataConstructorExp;
import de.uka.ilkd.keyabs.abs.expression.ABSFnApp;
import de.uka.ilkd.keyabs.abs.expression.ABSIntLiteral;
import de.uka.ilkd.keyabs.abs.expression.ABSMinusExp;
import de.uka.ilkd.keyabs.abs.expression.ABSNullExp;

/**
 * The front end for the Sequent pretty-printer. It prints a sequent and its
 * parts and computes the PositionTable, which is needed for highliting.
 * 
 * <P>
 * The actual layouting/formatting is done using the
 * {@link de.uka.ilkd.key.util.pp.Layouter} class. The concrete syntax for
 * operators is given by an instance of {@link NotationInfo}. The LogicPrinter
 * is responsible for the concrete <em>layout</em>, e.g. how terms with infix
 * operators are indented, and it binds the various needed components together.
 * 
 * @see NotationInfo
 * @see Notation
 * @see de.uka.ilkd.key.util.pp.Layouter
 * 
 * 
 */
public final class LogicPrinter implements ILogicPrinter {



    /**
     * A {@link de.uka.ilkd.key.util.pp.Backend} which puts its result in a
     * StringBuffer and builds a PositionTable. Position table construction is
     * done using the {@link de.uka.ilkd.key.util.pp.Layouter#mark(Object)}
     * facility of the layouter with the various static <code>MARK_</code>
     * objects declared {@link LogicPrinter}.
     */
    private static class PosTableStringBackend extends StringBackend {

        /** The top PositionTable */
        private final InitialPositionTable initPosTbl = new InitialPositionTable();

        /** The resulting position table or an intermediate result */
        private PositionTable posTbl = initPosTbl;

        /** The position in result where the current subterm starts */
        private int pos = 0;

        /**
         * The stack of StackEntry representing the nodes above the current
         * subterm
         */
        private final Stack<StackEntry> stack = new Stack<StackEntry>();

        /**
         * If this is set, a ModalityPositionTable will be built next.
         */
        private boolean need_modPosTable = false;

        /**
         * These two remember the range corresponding to the first executable
         * statement in a JavaBlock
         */
        private int firstStmtStart;
        private Range firstStmtRange;

        /** Remembers the start of an update to create a range */
        private final Stack<Integer> updateStarts = new Stack<Integer>();

        PosTableStringBackend(int lineWidth) {
            super(lineWidth);
        }

        /**
         * Returns the constructed position table.
         * 
         * @return the constructed position table
         */
        public InitialPositionTable getPositionTable() {
            return initPosTbl;
        }

        /**
         * Receive a mark and act appropriately.
         */
        @Override
        public void mark(Object o) {

            // IMPLEMENTATION NOTE
            //
            // This if-cascade is really ugly. In paricular the part
            // which says <code>instanceof Integer</code>, which stand
            // for a startTerm with given arity.
            //
            // The alternative would be to 1.: spread these
            // mini-functionalties across several inner classes in a
            // visitor-like style, effectively preventing anybody from
            // finding out what happens, and 2.: allocate separate
            // objects for each startTerm call to wrap the arity.
            //
            // I (MG) prefer it this way.
            if (o == MARK_START_SUB) {
                posTbl.setStart(count() - pos);
                stack.push(new StackEntry(posTbl, pos));
                pos = count();
            } else if (o == MARK_END_SUB) {
                StackEntry se = stack.peek();
                stack.pop();
                pos = se.pos();
                se.posTbl().setEnd(count() - pos, posTbl);
                posTbl = se.posTbl();
            } else if (o == MARK_MODPOSTBL) {
                need_modPosTable = true;
            } else if (o instanceof Integer) {
                // This is sent by startTerm
                int rows = ((Integer) o).intValue();
                if (need_modPosTable) {
                    posTbl = new ModalityPositionTable(rows);
                } else {
                    posTbl = new PositionTable(rows);
                }
                need_modPosTable = false;
            } else if (o == MARK_START_FIRST_STMT) {
                firstStmtStart = count() - pos;
            } else if (o == MARK_END_FIRST_STMT) {
                firstStmtRange = new Range(firstStmtStart, count() - pos);
                ((ModalityPositionTable) posTbl)
                        .setFirstStatementRange(firstStmtRange);
            } else if (o == MARK_START_UPDATE) {
                updateStarts.push(count());
            } else if (o == MARK_END_UPDATE) {
                int updateStart = updateStarts.pop();
                initPosTbl.addUpdateRange(new Range(updateStart, count()));
            }
        }
    }

    /**
     * Utility class for stack entries containing the position table and the
     * position of the start of the subterm in the result.
     */
    private static class StackEntry {

        PositionTable posTbl;
        int p;

        StackEntry(PositionTable posTbl, int p) {
            this.posTbl = posTbl;
            this.p = p;
        }

        int pos() {
            return p;
        }

        PositionTable posTbl() {
            return posTbl;
        }

    }

    /**
     * The default and minimal value o fthe max. number of characters to put in
     * one line
     */
    public static final int DEFAULT_LINE_WIDTH = 55;

    /** Mark the start of a subterm. Needed for PositionTable construction. */
    private static final Object MARK_START_SUB = new Object();

    /** Mark the end of a subterm. Needed for PositionTable construction. */
    private static final Object MARK_END_SUB = new Object();

    /**
     * Mark the start of the first executable statement. Needed for
     * PositionTable construction.
     */
    private static final Object MARK_START_FIRST_STMT = new Object();

    /**
     * Mark the end of the first executable statement. Needed for PositionTable
     * construction.
     */
    private static final Object MARK_END_FIRST_STMT = new Object();

    /**
     * Mark the need for a ModalityPositionTable. The next startTerm mark will
     * construct a ModalityPositionTable instead of the usual PositionTable.
     * Needed for PositionTable construction.
     */
    private static final Object MARK_MODPOSTBL = new Object();

    /** Mark the start of an update. */
    private static final Object MARK_START_UPDATE = new Object();

    /** Mark the end of an update. */
    private static final Object MARK_END_UPDATE = new Object();

    /**
     * escapes special characters by their HTML encoding
     * 
     * @param text
     *            the String to be displayed as part of an HTML side
     * @return the text with special characters replaced
     */
    public static String escapeHTML(String text, boolean escapeWhitespace) {
        StringBuffer sb = new StringBuffer();

        for (int i = 0, sz = text.length(); i < sz; i++) {
            char c = text.charAt(i);
            switch (c) {
            case '<':
                sb.append("&lt;");
                break;
            case '>':
                sb.append("&gt;");
                break;
            case '&':
                sb.append("&amp;");
                break;
            case '\"':
                sb.append("&quot;");
                break;
            case '\'':
                sb.append("&#039;");
                break;
            case '(':
                sb.append("&#040;");
                break;
            case ')':
                sb.append("&#041;");
                break;
            case '#':
                sb.append("&#035;");
                break;
            case '+':
                sb.append("&#043;");
                break;
            case '-':
                sb.append("&#045;");
                break;
            case '%':
                sb.append("&#037;");
                break;
            case ';':
                sb.append("&#059;");
                break;
            case '\n':
                sb.append(escapeWhitespace ? "<br>" : c);
                break;
            case ' ':
                sb.append(escapeWhitespace ? "&nbsp;" : c);
                break;
            default:
                sb.append(c);
            }

        }
        return sb.toString();
    }

    /**
     * tests if the program name together with the prefix sort determines the
     * attribute in a unique way
     * 
     * @param programName
     *            the String denoting the program name of the attribute
     * @param sort
     *            the ObjectSort specifying the hierarchy where to test for
     *            uniqueness
     * @param services
     *            the IServices class used to access the type hierarchy
     * @return true if the attribute is uniquely determined
     */
    public static boolean printInShortForm(String programName, Sort sort,
            Services services) {
        if (!(services != null && sort.extendsTrans(services.getJavaInfo()
                .objectSort()))) {
            return false;
        }
        final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
        assert kjt != null : "Did not find KeYJavaType for " + sort;
        return services.getJavaInfo().getAllAttributes(programName, kjt).size() == 1;
    }

    public static String quickPrintSemisequent(Semisequent s, IServices services) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services);
        }
        ILogicPrinter p = new LogicPrinter(services.getUIConfiguration()
                .createDefaultProgramPrinter(), ni, services);

        try {
            p.printSemisequent(s);
        } catch (IOException e) {
            return s.toString();
        }
        return p.result().toString();
    }

    public static String quickPrintSequent(Sequent s, IServices services) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services);
        }
        ILogicPrinter p = new LogicPrinter(services.getUIConfiguration()
                .createDefaultProgramPrinter(), ni, services);
        p.printSequent(s);
        return p.result().toString();
    }

    public static String quickPrintTerm(Term t, IServices services) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services);
        }
        ILogicPrinter p = new LogicPrinter(services.getUIConfiguration()
                .createDefaultProgramPrinter(), ni, services);
        try {
            p.printTerm(t);
        } catch (IOException ioe) {
            return t.toString();
        }
        return p.result().toString();
    }

    private static Set<SchemaVariable> collectSchemaVars(Taclet t) {

        Set<SchemaVariable> result = new HashSet<SchemaVariable>();
        OpCollector oc = new OpCollector();

        // find, assumes
        for (SchemaVariable sv : t.getIfFindVariables()) {
            result.add(sv);
        }

        // add, replacewith
        for (TacletGoalTemplate tgt : t.goalTemplates()) {
            collectSchemaVarsHelper(tgt.sequent(), oc);
            if (tgt instanceof AntecSuccTacletGoalTemplate) {
                collectSchemaVarsHelper(
                        ((AntecSuccTacletGoalTemplate) tgt).replaceWith(), oc);
            } else if (tgt instanceof RewriteTacletGoalTemplate) {
                ((RewriteTacletGoalTemplate) tgt).replaceWith().execPostOrder(
                        oc);
            }
        }

        for (Operator op : oc.ops()) {
            if (op instanceof SchemaVariable) {
                result.add((SchemaVariable) op);
            }
        }

        return result;
    }

    private static void collectSchemaVarsHelper(Sequent s, OpCollector oc) {
        for (SequentFormula cf : s) {
            cf.formula().execPostOrder(oc);
        }
    }

    /** The max. number of characters to put in one line */
    private int lineWidth = DEFAULT_LINE_WIDTH;

    /**
     * The ProgramPrinter used to pretty-print Java blocks in formulae.
     */
    private ProgramPrinter prgPrinter;

    /** Contains information on the concrete syntax of operators. */
    private final INotationInfo notationInfo;

    /** the services object */
    private final IServices services;

    /** This chooses the layout. */
    private Layouter layouter;

    /** The backend <code>layouter</code> will write to. */
    private Backend backend;

    /** If pure is true the PositionTable will not be calculated */
    private boolean pure = false;

    private SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    private boolean createPositionTable = true;

    private ABSProgramPrettyPrinter programPrettyPrinter = new ABSProgramPrettyPrinter(
            this);

    /**
     * Creates a LogicPrinter. Sets the sequent to be printed, as well as a
     * ProgramPrinter to print Java programs and a NotationInfo which determines
     * the concrete syntax.
     * 
     * @param prgPrinter
     *            the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo
     *            the NotationInfo for the concrete syntax
     * @param backend
     *            the Backend for the output
     * @param purePrint
     *            if true the PositionTable will not be calculated (simulates
     *            the behaviour of the former PureSequentPrinter)
     */
    public LogicPrinter(ProgramPrinter prgPrinter, INotationInfo notationInfo,
            Backend backend, IServices services, boolean purePrint) {
        this.backend = backend;
        this.layouter = new Layouter(backend, 2);
        this.prgPrinter = prgPrinter;
        this.notationInfo = notationInfo;
        this.services = services;
        this.pure = purePrint;
        if (services != null) {
            notationInfo.refresh(services);
        }
    }

    /**
     * Creates a LogicPrinter. Sets the sequent to be printed, as well as a
     * ProgramPrinter to print Java programs and a NotationInfo which determines
     * the concrete syntax.
     * 
     * @param prgPrinter
     *            the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo
     *            the NotationInfo for the concrete syntax
     * @param services
     *            The IServices object
     */
    public LogicPrinter(ProgramPrinter prgPrinter, INotationInfo notationInfo,
            IServices services) {
        this(prgPrinter, notationInfo, new PosTableStringBackend(
                DEFAULT_LINE_WIDTH), services, false);
    }

    /**
     * Creates a LogicPrinter. Sets the sequent to be printed, as well as a
     * ProgramPrinter to print Java programs and a NotationInfo which determines
     * the concrete syntax.
     * 
     * @param prgPrinter
     *            the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo
     *            the NotationInfo for the concrete syntax
     * @param purePrint
     *            if true the PositionTable will not be calculated (simulates
     *            the behaviour of the former PureSequentPrinter)
     * @param services
     *            the IServices object
     */
    public LogicPrinter(ProgramPrinter prgPrinter, INotationInfo notationInfo,
            IServices services, boolean purePrint) {
        this(prgPrinter, notationInfo, new PosTableStringBackend(
                DEFAULT_LINE_WIDTH), services, purePrint);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#getInstantiations()
     */
    @Override
    public SVInstantiations getInstantiations() {
        return instantiations;
    }

    /**
     * Returns the Layouter
     * 
     * @return the Layouter
     */
    @Override
    public Layouter getLayouter() {
        return layouter;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#getNotationInfo()
     */
    @Override
    public INotationInfo getNotationInfo() {
        return notationInfo;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#getPositionTable()
     */
    @Override
    public InitialPositionTable getPositionTable() {
        if (pure) {
            return null;
        }
        return ((PosTableStringBackend) backend).getPositionTable();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#printCast(java.lang.String,
     * java.lang.String, de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printCast(String pre, String post, Term t, int ass)
            throws IOException {
        final SortDependingFunction cast = (SortDependingFunction) t.op();

        startTerm(t.arity());
        layouter.print(pre);
        layouter.print(cast.getSortDependingOn().toString());
        layouter.print(post);
        maybeParens(t.sub(0), ass);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#printConstant(java.lang.String)
     */
    @Override
    public void printConstant(String s) throws IOException {

        startTerm(0);
        layouter.print(s);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printConstrainedFormula(de.uka.ilkd
     * .key.logic.SequentFormula)
     */
    @Override
    public void printConstrainedFormula(SequentFormula cfma) throws IOException {
        printTerm(cfma.formula());
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printElementaryUpdate(java.lang.String
     * , de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printElementaryUpdate(String asgn, Term t, int ass2)
            throws IOException {
        ElementaryUpdate op = (ElementaryUpdate) t.op();

        assert t.arity() == 1;
        startTerm(1);

        layouter.print(op.lhs().name().toString());

        layouter.print(asgn);

        maybeParens(t.sub(0), ass2);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printElementOf(de.uka.ilkd.key.logic
     * .Term)
     */
    @Override
    public void printElementOf(Term t) throws IOException {
        assert t.arity() == 3;
        startTerm(3);

        layouter.print("(").beginC(0);

        markStartSub();
        printTerm(t.sub(0));
        markEndSub();

        layouter.print(",").brk(1, 0);

        markStartSub();
        printTerm(t.sub(1));
        markEndSub();

        layouter.print(")").end();
        layouter.print(" \\in ");

        markStartSub();
        printTerm(t.sub(2));
        markEndSub();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printElementOf(de.uka.ilkd.key.logic
     * .Term, java.lang.String)
     */
    @Override
    public void printElementOf(Term t, String symbol) throws IOException {
        if (symbol == null) {
            printElementOf(t);
            return;
        }

        assert t.arity() == 3;
        startTerm(3);

        layouter.print("(").beginC(0);

        markStartSub();
        printTerm(t.sub(0));
        markEndSub();

        layouter.print(",").brk(1, 0);

        markStartSub();
        printTerm(t.sub(1));
        markEndSub();

        layouter.print(")").end();
        layouter.print(symbol);

        markStartSub();
        printTerm(t.sub(2));
        markEndSub();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printFunctionTerm(java.lang.String,
     * de.uka.ilkd.key.logic.Term)
     */
    @Override
    public void printFunctionTerm(String name, Term t) throws IOException {
        // XXX
        startTerm(t.arity());
        layouter.print(name);
        if (!t.boundVars().isEmpty()) {
            layouter.print("{").beginC(0);
            printVariables(t.boundVars());
            layouter.print("}").end();
        }
        if (t.arity() > 0) {
            layouter.print("(").beginC(0);
            for (int i = 0, n = t.arity(); i < n; i++) {
                markStartSub();
                printTerm(t.sub(i));
                markEndSub();

                if (i < n - 1) {
                    layouter.print(",").brk(1, 0);
                }
            }
            layouter.print(")").end();
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printIfThenElseTerm(de.uka.ilkd.key
     * .logic.Term, java.lang.String)
     */
    @Override
    public void printIfThenElseTerm(Term t, String keyword) throws IOException {
        startTerm(t.arity());

        layouter.beginC(0);

        layouter.print(keyword);

        assert t.boundVars().isEmpty();

        layouter.print(" (");
        markStartSub();
        printTerm(t.sub(0));
        markEndSub();
        layouter.print(")");

        for (int i = 1; i < t.arity(); ++i) {
            layouter.brk(1, 3);
            if (i == 1) {
                layouter.print(" \\then (");
            } else {
                layouter.print(" \\else (");
            }
            markStartSub();
            printTerm(t.sub(i));
            markEndSub();
            layouter.print(")");
        }

        layouter.end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printInfixTerm(de.uka.ilkd.key.logic
     * .Term, int, java.lang.String, de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printInfixTerm(Term l, int assLeft, String name, Term r,
            int assRight) throws IOException {
        int indent = name.length() + 1;
        layouter.beginC(indent);
        printInfixTermContinuingBlock(l, assLeft, name, r, assRight);
        layouter.end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printInfixTermContinuingBlock(de.
     * uka.ilkd.key.logic.Term, int, java.lang.String,
     * de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printInfixTermContinuingBlock(Term l, int assLeft, String name,
            Term r, int assRight) throws IOException {
        int indent = name.length() + 1;
        startTerm(2);
        layouter.ind();
        maybeParens(l, assLeft);
        layouter.brk(1, -indent).print(name).ind(1, 0);
        maybeParens(r, assRight);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printInShortForm(java.lang.String,
     * de.uka.ilkd.key.logic.sort.Sort)
     */
    @Override
    public boolean printInShortForm(String programName, Sort sort) {
        return printInShortForm(programName, sort,
                services instanceof Services ? (Services) services : null);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printInShortForm(java.lang.String,
     * de.uka.ilkd.key.logic.Term)
     */
    @Override
    public boolean printInShortForm(String attributeProgramName, Term t) {
        final Sort prefixSort;
        prefixSort = t.sort();
        return printInShortForm(attributeProgramName, prefixSort);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printJavaBlock(de.uka.ilkd.key.logic
     * .JavaBlock)
     */
    @Override
    public void printJavaBlock(JavaBlock j) throws IOException {
        markFirstStatement = true;
        if (j.isEmpty()) {
            if (markFirstStatement) {
                markFirstStatement = false;
                mark(MARK_START_FIRST_STMT);
                mark(MARK_END_FIRST_STMT);
            }
        }
        j.program().visit(programPrettyPrinter);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printLength(de.uka.ilkd.key.logic
     * .Term)
     */
    @Override
    public void printLength(Term t) throws IOException {
        printFunctionTerm(t.op().name().toString(), t);
    }

    @Override
    public void printModalityTerm(String left, JavaBlock jb, String right,
            Term phi, int ass) throws IOException {
        assert jb != null;
        assert jb.program() != null;
        if (phi.op() instanceof ModalOperatorSV) {
            Object o = getInstantiations().getInstantiation(
                    (ModalOperatorSV) phi.op());
            if (o == null) {
                Debug.log4jDebug("PMT  NO  " + phi + " @[ " + phi.op() + " ]@ "
                        + " is : " + phi.getClass().getName() + " @["
                        + phi.op().getClass().getName() + "]@ known",
                        LogicPrinter.class.getName());
            } else {
                // logger.debug("Instantiation of " + phi + " @[" + phi.op() +
                // "]@" + " is : " + o + o.getClass().getName());
                // logger.debug(getInstantiations());
                Debug.log4jDebug("PMT YES " + phi.op() + " -> " + o + " @["
                        + o.getClass().getName() + "]@",
                        LogicPrinter.class.getName());

                Term[] ta = new Term[phi.arity()];
                for (int i = 0; i < phi.arity(); i++) {
                    ta[i] = phi.sub(i);
                }
                Term term = TermFactory.DEFAULT.createTerm((Modality) o, ta,
                        phi.boundVars(), phi.javaBlock());
                notationInfo.getNotation((Modality) o, services).print(term,
                        this);
                return;

            }
        }

        mark(MARK_MODPOSTBL);
        startTerm(phi.arity());
        layouter.beginC(2).ind().print(left);
        printJavaBlock(jb);
        layouter.ind(0, -2).print(right).end();

        if (phi.arity() == 1) {
            maybeParens(phi.sub(0), ass);
        } else if (phi.arity() > 1) {
            layouter.print("(");
            for (int i = 0; i < phi.arity(); i++) {
                markStartSub();
                printTerm(phi.sub(i));
                markEndSub();
                if (i < phi.arity() - 1) {
                    layouter.print(",").brk(1, 0);
                }
            }
            layouter.print(")");
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printObserver(de.uka.ilkd.key.logic
     * .Term)
     */
    @Override
    public void printObserver(Term t) throws IOException {
        assert t.op() instanceof IObserverFunction;
        assert t.boundVars().isEmpty();
        printFunctionTerm(t.op().name().toString(), t);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printParallelUpdate(java.lang.String,
     * de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printParallelUpdate(String separator, Term t, int ass)
            throws IOException {
        layouter.beginC(0);
        printParallelUpdateHelper(separator, t, ass);
        layouter.end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printPostfixTerm(de.uka.ilkd.key.
     * logic.Term, int, java.lang.String)
     */
    @Override
    public void printPostfixTerm(Term t, int ass, String name)
            throws IOException {
        startTerm(1);
        maybeParens(t, ass);
        layouter.print(name);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printPrefixTerm(java.lang.String,
     * de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printPrefixTerm(String name, Term t, int ass)
            throws IOException {
        startTerm(1);
        layouter.print(name);
        maybeParens(t, ass);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printProgramElement(de.uka.ilkd.key
     * .java.ProgramElement)
     */
    @Override
    public void printProgramElement(ProgramElement pe) throws IOException {
        if (pe instanceof ProgramVariable) {
            printProgramVariable((ProgramVariable) pe);
        } else {
            pe.visit(programPrettyPrinter);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printProgramSV(de.uka.ilkd.key.logic
     * .op.ProgramSV)
     */
    @Override
    public void printProgramSV(ProgramSV pe) throws IOException {
        StringWriter w = new StringWriter();
        PrettyPrinter pp = new PrettyPrinter(w, true, instantiations);
        pe.prettyPrint(pp);
        layouter.pre(w.toString());
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printProgramVariable(de.uka.ilkd.
     * key.logic.op.ProgramVariable)
     */
    @Override
    public void printProgramVariable(ProgramVariable pv) throws IOException {
        Debug.log4jDebug("PP PV " + pv.name(), LogicPrinter.class.getName());
        layouter.beginC().print(pv.name().toString()).end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printQuantifierTerm(java.lang.String,
     * de.uka.ilkd.key.collection.ImmutableArray, de.uka.ilkd.key.logic.Term,
     * int)
     */
    @Override
    public void printQuantifierTerm(String name,
            ImmutableArray<QuantifiableVariable> vars, Term phi, int ass)
            throws IOException {
        layouter.beginC(2);
        layouter.print(name).print(" ");
        printVariables(vars);
        layouter.brk();
        startTerm(1);
        maybeParens(phi, ass);
        layouter.end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSelect(de.uka.ilkd.key.logic
     * .Term)
     */
    @Override
    public void printSelect(Term t) throws IOException {
        assert t.boundVars().isEmpty();
        assert t.arity() == 3;
        printFunctionTerm(t.op().name().toString(), t);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSemisequent(de.uka.ilkd.key.
     * collection.ImmutableList)
     */
    @Override
    public void printSemisequent(
            ImmutableList<SequentPrintFilterEntry> p_formulas)
            throws IOException {
        Iterator<SequentPrintFilterEntry> it = p_formulas.iterator();
        SequentPrintFilterEntry entry;
        int size = p_formulas.size();
        while (size-- != 0) {
            entry = it.next();
            markStartSub();
            printConstrainedFormula(entry.getFilteredFormula());
            markEndSub();
            if (size != 0) {
                layouter.print(",").brk(1);
            }
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSemisequent(de.uka.ilkd.key.
     * logic.Semisequent)
     */
    @Override
    public void printSemisequent(Semisequent semiseq) throws IOException {
        for (int i = 0; i < semiseq.size(); i++) {
            markStartSub();
            printConstrainedFormula(semiseq.get(i));
            markEndSub();
            if (i != semiseq.size() - 1) {
                layouter.print(",").brk(1);
            }
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSequent(de.uka.ilkd.key.logic
     * .Sequent)
     */
    @Override
    public void printSequent(Sequent seq) {
        printSequent(seq, true);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSequent(de.uka.ilkd.key.logic
     * .Sequent, boolean)
     */
    @Override
    public void printSequent(Sequent seq, boolean finalbreak) {
        try {
            Semisequent antec = seq.antecedent();
            Semisequent succ = seq.succedent();
            markStartSub();
            startTerm(antec.size() + succ.size());
            layouter.beginC(1).ind();
            printSemisequent(antec);
            layouter.brk(1, -1).print("==>").brk(1);
            printSemisequent(succ);
            if (finalbreak) {
                layouter.brk(0);
            }
            markEndSub();
            layouter.end();
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException("Unbalanced blocks in pretty printer:\n"
                    + e);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSequent(de.uka.ilkd.key.logic
     * .Sequent, de.uka.ilkd.key.pp.SequentPrintFilter)
     */
    @Override
    public void printSequent(Sequent seq, SequentPrintFilter filter) {
        printSequent(seq, filter, true);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSequent(de.uka.ilkd.key.logic
     * .Sequent, de.uka.ilkd.key.pp.SequentPrintFilter, boolean)
     */
    @Override
    public void printSequent(Sequent seq, SequentPrintFilter filter,
            boolean finalbreak) {
        if (seq != null) {
            printSequent(seq, finalbreak);
        } else if (filter != null) {
            printSequent(filter, finalbreak);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#printSequent(de.uka.ilkd.key.pp.
     * SequentPrintFilter, boolean)
     */
    @Override
    public void printSequent(SequentPrintFilter filter, boolean finalbreak) {
        try {
            ImmutableList<SequentPrintFilterEntry> antec = filter.getAntec();
            ImmutableList<SequentPrintFilterEntry> succ = filter.getSucc();
            markStartSub();
            startTerm(antec.size() + succ.size());
            layouter.beginC(1).ind();
            printSemisequent(antec);
            layouter.brk(1, -1).print("==>").brk(1);
            printSemisequent(succ);
            if (finalbreak) {
                layouter.brk(0);
            }
            markEndSub();
            layouter.end();
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException("Unbalanced blocks in pretty printer:\n"
                    + e);
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printSingleton(de.uka.ilkd.key.logic
     * .Term)
     */
    @Override
    public void printSingleton(Term t) throws IOException {
        assert t.arity() == 2;
        startTerm(2);
        layouter.print("{(").beginC(0);
        ;

        markStartSub();
        printTerm(t.sub(0));
        markEndSub();

        layouter.print(",").brk(1, 0);

        markStartSub();
        printTerm(t.sub(1));
        markEndSub();

        layouter.print(")}").end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#printSubstTerm(java.lang.String,
     * de.uka.ilkd.key.logic.op.QuantifiableVariable,
     * de.uka.ilkd.key.logic.Term, int, java.lang.String,
     * de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printSubstTerm(String l, QuantifiableVariable v, Term t,
            int ass2, String r, Term phi, int ass3) throws IOException {
        layouter.beginC(2).print(l);
        printVariables(new ImmutableArray<QuantifiableVariable>(v));
        startTerm(2);
        maybeParens(t, ass2);
        layouter.print(r).brk(0);
        maybeParens(phi, ass3);
        layouter.end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printTaclet(de.uka.ilkd.key.rule.
     * Taclet)
     */
    @Override
    public void printTaclet(Taclet taclet) {
        // the last argument used to be false. Changed that - M.Ulbrich
        printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true, true);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printTaclet(de.uka.ilkd.key.rule.
     * Taclet, de.uka.ilkd.key.rule.inst.SVInstantiations, boolean, boolean)
     */
    @Override
    public void printTaclet(Taclet taclet, SVInstantiations sv,
            boolean showWholeTaclet, boolean declareSchemaVars) {
        instantiations = sv;
        try {
            Debug.log4jDebug(taclet.name().toString(),
                    LogicPrinter.class.getName());
            if (showWholeTaclet) {
                layouter.beginC(2).print(taclet.name().toString()).print(" {");
            } else {
                layouter.beginC();
            }
            if (declareSchemaVars) {
                Set<SchemaVariable> schemaVars = collectSchemaVars(taclet);
                layouter.brk();
                for (SchemaVariable schemaVar : schemaVars) {
                    layouter.print(schemaVar.proofToString() + "  ");
                }
            }
            if (!(taclet.ifSequent().isEmpty())) {
                printTextSequent(taclet.ifSequent(), "\\assumes", true);
            }
            if (showWholeTaclet) {
                printFind(taclet);
                if (taclet instanceof RewriteTaclet) {
                    printRewriteAttributes((RewriteTaclet) taclet);
                }
                printVarCond(taclet);
            }
            printGoalTemplates(taclet);
            if (showWholeTaclet) {
                printHeuristics(taclet);
            }
            if (showWholeTaclet) {
                layouter.brk(1, -2).print("}");
            }
            layouter.end();
        } catch (java.io.IOException e) {
            Debug.log4jWarn("xxx exception occurred during printTaclet",
                    LogicPrinter.class.getName());
        }
        instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printTerm(de.uka.ilkd.key.collection
     * .ImmutableSet)
     */
    @Override
    public void printTerm(ImmutableSet<Term> terms) throws IOException {
        getLayouter().print("{");
        Iterator<Term> it = terms.iterator();
        while (it.hasNext()) {
            printTerm(it.next());
            if (it.hasNext())
                getLayouter().print(", ");
        }
        getLayouter().print("}");
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printTerm(de.uka.ilkd.key.logic.Term)
     */
    @Override
    public void printTerm(Term t) throws IOException {
        notationInfo.getNotation(t.op(), services).print(t, this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printTermContinuingBlock(de.uka.ilkd
     * .key.logic.Term)
     */
    @Override
    public void printTermContinuingBlock(Term t) throws IOException {
        notationInfo.getNotation(t.op(), services)
                .printContinuingBlock(t, this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#printUpdateApplicationTerm(java.lang
     * .String, java.lang.String, de.uka.ilkd.key.logic.Term, int)
     */
    @Override
    public void printUpdateApplicationTerm(String l, String r, Term t, int ass3)
            throws IOException {
        assert t.op() instanceof UpdateApplication && t.arity() == 2;

        mark(MARK_START_UPDATE);
        layouter.beginC(2).print(l);
        startTerm(t.arity());

        markStartSub();
        printTerm(t.sub(0));
        markEndSub();

        layouter.print(r);
        mark(MARK_END_UPDATE);
        layouter.brk(0);

        maybeParens(t.sub(1), ass3);

        layouter.end();
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#programPrinter()
     */
    @Override
    public ProgramPrinter programPrinter() {
        return prgPrinter;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#reset()
     */
    @Override
    public void reset() {
        backend = new PosTableStringBackend(lineWidth);
        layouter = new Layouter(backend, 2);
        if (prgPrinter != null) {
            prgPrinter.reset();
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#result()
     */
    @Override
    public StringBuffer result() {
        try {
            layouter.flush();
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        }
        return new StringBuffer(((PosTableStringBackend) backend).getString())
                .append("\n");
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#setInstantiation(de.uka.ilkd.key.
     * rule.inst.SVInstantiations)
     */
    @Override
    public void setInstantiation(SVInstantiations instantiations) {
        this.instantiations = instantiations;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#setLineWidth(int)
     */
    @Override
    public int setLineWidth(int lineWidth) {
        this.lineWidth = lineWidth < DEFAULT_LINE_WIDTH ? DEFAULT_LINE_WIDTH
                : lineWidth;
        return this.lineWidth;
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.keyabs.pp.ILogicPrinter#toString()
     */
    @Override
    public String toString() {
        try {
            layouter.flush();
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        }
        return ((PosTableStringBackend) backend).getString() + "\n";
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.keyabs.pp.ILogicPrinter#update(de.uka.ilkd.key.logic.Sequent,
     * de.uka.ilkd.key.pp.SequentPrintFilter, int)
     */
    @Override
    public void update(Sequent seq, SequentPrintFilter filter, int lineWidth) {
        setLineWidth(lineWidth);
        reset();
        printSequent(seq, filter);
    }


    private void printNewVarDepOnCond(NewDependingOn on) throws IOException {
        layouter.beginC(0);
        layouter.brk().print("\\new( ");
        printSchemaVariable(on.first());
        layouter.print(",").brk();
        layouter.print("\\dependingOn(");
        printSchemaVariable(on.second());
        layouter.brk(0, -2).print(")").brk();
        layouter.brk(0, -2).print(")").end();
    }

    private void printParallelUpdateHelper(String separator, Term t, int ass)
            throws IOException {
        assert t.arity() == 2;
        startTerm(2);

        if (t.sub(0).op() == UpdateJunctor.PARALLEL_UPDATE) {
            markStartSub();
            printParallelUpdateHelper(separator, t.sub(0), ass);
            markEndSub();
        } else {
            maybeParens(t.sub(0), ass);
        }

        layouter.brk(1).print(separator + " ");

        if (t.sub(1).op() == UpdateJunctor.PARALLEL_UPDATE) {
            markStartSub();
            printParallelUpdateHelper(separator, t.sub(1), ass);
            markEndSub();
        } else {
            maybeParens(t.sub(1), ass);
        }
    }

    protected Layouter mark(Object o) {
        if (pure) {
            return null;
        } else {
            return layouter.mark(o);
        }
    }

    /**
     * Called after a substring is printed that has its own entry in a position
     * table. The backend will finishes the position table on the top of the
     * stack and set the entry on the top of the stack to be the current
     * position/position table. Subclasses may overwrite this method with an
     * empty body if position information is not needed there.
     */
    protected void markEndSub() {
        if (createPositionTable) {
            mark(MARK_END_SUB);
        }
    }

    /**
     * Called before a substring is printed that has its own entry in a position
     * table. The method sends a mark to the layouter, which will make the
     * backend set a start entry in posTbl, push a new StackEntry with the
     * current posTbl and current pos on the stack and set the current pos to
     * the length of the current string result. Subclasses may overwrite this
     * method with an empty body if position information is not needed there.
     */
    protected void markStartSub() {
        if (createPositionTable) {
            mark(MARK_START_SUB);
        }
    }

    /**
     * Prints a subterm, if needed with parentheses. Each subterm has a
     * Priority. If the priority is less than the associativity for that subterm
     * fixed by the Notation/NotationInfo, parentheses are needed.
     * 
     * <p>
     * If prio and associativity are equal, the subterm is printed using
     * {@link #printTermContinuingBlock(Term)}. This currently only makes a
     * difference for infix operators.
     * 
     * @param t
     *            the the subterm to print
     * @param ass
     *            the associativity for this subterm
     */
    protected void maybeParens(Term t, int ass) throws IOException {
        if (t.op() instanceof SchemaVariable
                && instantiations != null
                && instantiations.getInstantiation((SchemaVariable) t.op()) instanceof Term) {
            t = (Term) instantiations.getInstantiation((SchemaVariable) t.op());
        }

        if (notationInfo.getNotation(t.op(), services).getPriority() < ass) {
            markStartSub();
            layouter.print("(");
            printTerm(t);
            layouter.print(")");
            markEndSub();
        } else {
            markStartSub();
            if (notationInfo.getNotation(t.op(), services).getPriority() == ass) {
                printTermContinuingBlock(t);
            } else {
                printTerm(t);
            }
            markEndSub();
        }
    }

    protected void printAddProgVars(ImmutableSet<SchemaVariable> apv)
            throws IOException {
        layouter.beginC(2).print("\\addprogvars (");
        for (Iterator<SchemaVariable> it = apv.iterator(); it.hasNext();) {
            layouter.brk();
            SchemaVariable tgt = it.next();
            printSchemaVariable(tgt);
            if (it.hasNext()) {
                layouter.print(",");
            }
        }
        layouter.brk(1, -2).print(")").end();
    }

    protected void printFind(Taclet taclet) throws IOException {
        if (!(taclet instanceof FindTaclet)) {
            return;
        }
        layouter.brk().beginC(2).print("\\find (").brk();
        if (taclet instanceof SuccTaclet) {
            layouter.print("==>").brk();
        }
        printTerm(((FindTaclet) taclet).find());
        if (taclet instanceof AntecTaclet) {
            layouter.brk().print("==>");
        }
        layouter.brk(1, -2).print(")").end();
    }

    protected void printGoalTemplate(TacletGoalTemplate tgt) throws IOException {
        // layouter.beginC(0);
        if (tgt.name() != null) {
            if (tgt.name().length() > 0) {
                layouter.brk().beginC(2).print("\"" + tgt.name() + "\"")
                        .print(":");
            }

        }
        if (tgt instanceof AntecSuccTacletGoalTemplate) {
            printTextSequent(((AntecSuccTacletGoalTemplate) tgt).replaceWith(),
                    "\\replacewith", true);
        }
        if (tgt instanceof RewriteTacletGoalTemplate) {
            layouter.brk();
            printRewrite(((RewriteTacletGoalTemplate) tgt).replaceWith());
        }

        if (!(tgt.sequent().isEmpty())) {
            printTextSequent(tgt.sequent(), "\\add", true);
        }
        if (!tgt.rules().isEmpty()) {
            printRules(tgt.rules());
        }
        if (tgt.addedProgVars().size() > 0) {
            layouter.brk();
            printAddProgVars(tgt.addedProgVars());
        }

        if (tgt.name() != null) {
            if (tgt.name().length() > 0) {
                layouter.brk(1, -2).end();
            }
        }
        // layouter.end();
    }

    protected void printGoalTemplates(Taclet taclet) throws IOException {
        // layouter.beginC(0);
        if (taclet.closeGoal()) {
            layouter.brk().print("\\closegoal").brk();
        }

        for (final Iterator<TacletGoalTemplate> it = taclet.goalTemplates()
                .reverse().iterator(); it.hasNext();) {
            printGoalTemplate(it.next());
            if (it.hasNext()) {
                layouter.print(";");
            }
        }
        // layouter.end();
    }

    protected void printHeuristic(RuleSet sv) throws IOException {
        layouter.print(sv.name().toString());
    }

    protected void printHeuristics(Taclet taclet) throws IOException {
        if (taclet.getRuleSets().size() == 0) {
            return;
        }
        layouter.brk().beginC(2).print("\\heuristics (");
        for (Iterator<RuleSet> it = taclet.getRuleSets().iterator(); it
                .hasNext();) {
            layouter.brk();
            RuleSet tgt = it.next();
            printHeuristic(tgt);
            if (it.hasNext()) {
                layouter.print(",");
            }
        }
        layouter.brk(1, -2).print(")").end();
    }

    protected void printNewVarcond(NewVarcond sv) throws IOException {
        layouter.beginC(0);
        layouter.brk().print("\\new(");
        printSchemaVariable(sv.getSchemaVariable());
        layouter.print(",").brk();
        if (sv.isDefinedByType()) {
            if (sv.getType() instanceof ArrayType) {
                layouter.print(((ArrayType) sv.getType())
                        .getAlternativeNameRepresentation());
            } else {
                layouter.print(sv.getType().getFullName());
            }
        } else {
            layouter.print("\\typeof (").brk();
            printSchemaVariable(sv.getPeerSchemaVariable());
            layouter.brk(0, -2).print(")").brk();
        }
        layouter.brk(0, -2).print(")").end();
    }

    protected void printNotFreeIn(NotFreeIn sv) throws IOException {
        layouter.beginI(0);
        layouter.brk().print("\\notFreeIn(").brk();
        printSchemaVariable(sv.first());
        layouter.print(",").brk();
        printSchemaVariable(sv.second());
        layouter.brk(0, -2).print(")").end();
    }

    protected void printRewrite(Term t) throws IOException {
        layouter.beginC(2).print("\\replacewith (").brk();
        printTerm(t);
        layouter.brk(1, -2).print(")").end();
    }

    protected void printRewriteAttributes(RewriteTaclet taclet)
            throws IOException {
        final int stateRestriction = taclet.getApplicationRestriction();
        if (stateRestriction == RewriteTaclet.SAME_UPDATE_LEVEL) {
            layouter.brk().print("\\sameUpdateLevel");
        } else if (stateRestriction == RewriteTaclet.IN_SEQUENT_STATE) {
            layouter.brk().print("\\inSequentState");
        } else if (stateRestriction == RewriteTaclet.ANTECEDENT_POLARITY) {
            layouter.brk().print("\\antecedentPolarity");
        } else if (stateRestriction == RewriteTaclet.SAME_UPDATE_LEVEL) {
            layouter.brk().print("\\succedentPolarity");
        }
    }

    protected void printRules(ImmutableList<Taclet> rules) throws IOException {
        layouter.brk().beginC(2).print("\\addrules (");
        SVInstantiations svi = instantiations;
        for (Iterator<Taclet> it = rules.iterator(); it.hasNext();) {
            layouter.brk();
            Taclet t = it.next();
            printTaclet(t, instantiations, true, false);
            instantiations = svi;
        }
        layouter.brk(1, -2).print(")").end();
    }

    protected void printSchemaVariable(SchemaVariable sv) throws IOException {
        Object o = getInstantiations().getInstantiation(sv);
        if (o == null) {
            if (sv instanceof ProgramSV) {
                printProgramSV((ProgramSV) sv);
            } else {
                printConstant(sv.name().toString());
            }
        } else {
            if (o instanceof Term) {
                printTerm((Term) o);
            } else if (o instanceof ProgramElement) {
                printProgramElement((ProgramElement) o);
            } else {
                Debug.log4jWarn("Unknown instantiation type of " + o
                        + "; class is " + o.getClass().getName(),
                        LogicPrinter.class.getName());
                printConstant(sv.name().toString());
            }
        }
    }

    protected void printTextSequent(Sequent seq, String text, boolean frontbreak)
            throws IOException {

        if (frontbreak) {
            layouter.brk();
        }

        layouter.beginC(2).print(text).print(" (");
        printSequent(seq, null, false);
        layouter.brk(1, -2).print(")").end();
    }

    protected void printVarCond(Taclet taclet) throws IOException {
        Iterator<NewVarcond> itVarsNew = taclet.varsNew().iterator();
        Iterator<NewDependingOn> itVarsNewDepOn = taclet.varsNewDependingOn();
        Iterator<NotFreeIn> itVarsNotFreeIn = taclet.varsNotFreeIn();
        Iterator<VariableCondition> itVC = taclet.getVariableConditions();

        if (itVarsNew.hasNext() || itVarsNotFreeIn.hasNext() || itVC.hasNext()
                || itVarsNewDepOn.hasNext()) {
            layouter.brk().beginC(2).print("\\varcond (").brk();
            while (itVarsNewDepOn.hasNext()) {
                printNewVarDepOnCond(itVarsNewDepOn.next());
                if (itVarsNewDepOn.hasNext() || itVarsNew.hasNext()
                        || itVarsNotFreeIn.hasNext() || itVC.hasNext()) {
                    layouter.print(",").brk();
                }
            }
            while (itVarsNew.hasNext()) {
                printNewVarcond(itVarsNew.next());
                if (itVarsNew.hasNext() || itVarsNotFreeIn.hasNext()
                        || itVC.hasNext()) {
                    layouter.print(",").brk();
                }
            }
            while (itVarsNotFreeIn.hasNext()) {
                NotFreeIn pair = itVarsNotFreeIn.next();
                printNotFreeIn(pair);
                if (itVarsNotFreeIn.hasNext() || itVC.hasNext()) {
                    layouter.print(",").brk();
                }
            }
            while (itVC.hasNext()) {
                printVariableCondition(itVC.next());
                if (itVC.hasNext()) {
                    layouter.print(",").brk();
                }
            }
            layouter.brk(1, -2).print(")").end();
        }
    }

    protected void printVariableCondition(VariableCondition<ABSServices> sv)
            throws IOException {
        layouter.print(sv.toString());
    }

    protected void printVariables(ImmutableArray<QuantifiableVariable> vars)
            throws IOException {
        int size = vars.size();
        for (int j = 0; j != size; j++) {
            final QuantifiableVariable v = vars.get(j);
            if (v instanceof LogicVariable) {
                layouter.print(v.sort().name() + " " + v.name());
            } else {
                layouter.print(v.name().toString());
            }
            if (j < size - 1) {
                layouter.print(", ");
            }
        }
        layouter.print(";");
    }

    /**
     * Start a term with subterms. The backend will set the current posTbl to a
     * newly created position table with the given number of rows. Subclasses
     * may overwrite this method with an empty body if position information is
     * not needed there.
     * 
     * @param size
     *            the number of rows of the new position table
     */
    protected void startTerm(int size) {
        if (createPositionTable) {
            mark(Integer.valueOf(size));
        }
    }

    public void printProgramElementName(ProgramElementName x)
            throws IOException {
        layouter.print(x.getProgramName().toString());
    }

    public void printLocationVariable(LocationVariable x) throws IOException {
        layouter.beginC().print(x.name().toString()).end();
    }

    private boolean markFirstStatement = false;

    public void printABSCopyAssignment(CopyAssignment x) throws IOException {
        layouter.beginI(2);
        x.getChildAt(0).visit(programPrettyPrinter);

        layouter.end().print(" = ").beginI(2);

        x.getChildAt(1).visit(programPrettyPrinter);

        layouter.print(";").end();
    }

    public void printABSFieldReference(ABSFieldReference x) throws IOException {
        layouter.print("this.").print(((ProgramElementName) x.getField().name()).getProgramName());
    }

    public void printABSLocalVariableReference(ABSLocalVariableReference x)
            throws IOException {
        layouter.print(x.getVariable().name().toString());
    }

    public void printThisExpression(ThisExpression x) throws IOException {
        layouter.beginC().print("this").end();
    }

    public void printABSStatementBlock(ABSStatementBlock x) throws IOException {
        layouter.print("{").beginC(2).ind();
        printStatementList(x);
        layouter.brk(0, -2).end().print("}");
    }

    private void printStatementList(StatementContainer x) throws IOException {
        if (x.getStatementCount() <= 0) {
        	return;
        }
        layouter.print(" ");
        for (int i = 0; i < x.getStatementCount(); i++) {
            final boolean fstStmnt = markFirstStatement &&
            		(!(x.getChildAt(i) instanceof ProgramPrefix) ||
                       (!(x.getChildAt(i) instanceof NonTerminalProgramElement) || 
                    		   ((NonTerminalProgramElement)x).getChildCount() == 0));
            if (fstStmnt) {
                markFirstStatement = false;
                mark(MARK_START_FIRST_STMT);
            }
            x.getStatementAt(i).visit(programPrettyPrinter);
            if (fstStmnt) {               
                mark(MARK_END_FIRST_STMT);
            }
            if (i < x.getStatementCount() - 1) {
                layouter.brk(1);
            }
        }
        layouter.print(" ");
    }

    public void printABSBinaryOpExp(ABSBinaryOperatorPureExp x, String op)
            throws IOException {
        layouter.beginI(2);
        x.getChildAt(0).visit(programPrettyPrinter);
        layouter.ind(1, 0).print(op).ind(1, 0);
        x.getChildAt(1).visit(programPrettyPrinter);
        layouter.end();
    }

    public void printABSVariableDeclarationStatement(
            ABSVariableDeclarationStatement x) throws IOException {
        layouter.beginC();
        x.getTypeReference().visit(programPrettyPrinter);
        layouter.brk(1);
        x.getVariable().visit(programPrettyPrinter);
        if (x.getInitializer() != null) {
            layouter.brk(1).print("=").brk(1);
            x.getInitializer().visit(programPrettyPrinter);
        }
        layouter.print(";").end();
    }

    public void printABSTypeReference(ABSTypeReference x) throws IOException {
        layouter.print(x.getName());
    }

    public void printABSAsyncMethodCall(ABSAsyncMethodCall x)
            throws IOException {
        x.getChildAt(0).visit(programPrettyPrinter);
        layouter.print("!");
        x.getChildAt(1).visit(programPrettyPrinter);
        layouter.beginC(0).print("(");
        for (int i = 0; i < x.getArgumentCount(); i++) {
            if (i != 0)
                layouter.print(",").brk(1);
            x.getArgumentAt(i).visit(programPrettyPrinter);
        }
        layouter.print(")").end();
    }

    public void printABSNullExp(ABSNullExp x) throws IOException {
        layouter.print("null");
    }

    public void printABSDataConstructorExp(ABSDataConstructorExp x)
            throws IOException {
        x.getChildAt(0).visit(programPrettyPrinter);
        if (x.getArgumentCount() > 0) {
            layouter.beginC(0).print("(");
            for (int i = 0; i < x.getArgumentCount(); i++) {
                if (i != 0)
                    layouter.print(",").brk(1);
                x.getArgumentAt(i).visit(programPrettyPrinter);
            }
            layouter.print(")").end();
        }
    }

    public void printABSIntLiteral(ABSIntLiteral x) throws IOException {
        layouter.print(x.getValue().toString());
    }

    public void printABSIfStatement(ABSIfStatement x) throws IOException {
        layouter.beginC(0).print("if (");
        x.getCondition().visit(programPrettyPrinter);
        layouter.print(")").brk(1, 2);
        x.getThenBranch().visit(programPrettyPrinter);
        layouter.brk(1);
        if (x.getElseBranch() != null) {
            layouter.print("else").brk(1, 2);
            x.getElseBranch().visit(programPrettyPrinter);
        } 
        layouter.ind().end();
    }

    public void printABSContextStatementBlock(ABSContextStatementBlock x)
            throws IOException {
        layouter.print("{..").beginC(2).brk(1);
        printStatementList(x);
        layouter.end().print("...}");
    }

    public void printABSMinusExp(ABSMinusExp x) throws IOException {
        layouter.print("-(");
        x.getChildAt(0).visit(programPrettyPrinter);
        layouter.print(")");
    }

    public void printABSWhileStatement(ABSWhileStatement x) throws IOException {
	 layouter.beginC(0).print("while (");
	 x.getCondition().visit(programPrettyPrinter);
	 layouter.print(")").brk(1, 2);
	 x.getBody().visit(programPrettyPrinter);
	 layouter.brk(1);
	 layouter.ind().end();
    }

    public void printABSAwaitStatement(ABSAwaitStatement x) throws IOException {
        layouter.beginC(0);
        layouter.print("await ");
        x.getCondition().visit(programPrettyPrinter);
        if (x instanceof ABSAwaitClaimStatement) {
            layouter.print("?");
        }
        layouter.print(";").brk(1);
        layouter.ind().end();
    }

    public void printABSFnApp(ABSFnApp x) throws IOException {
        x.getChildAt(0).visit(programPrettyPrinter);
        layouter.beginC(0).print("(");
        for (int i = 0; i < x.getArgumentCount(); i++) {
            if (i != 0)
                layouter.print(",").brk(1);
            x.getArgumentAt(i).visit(programPrettyPrinter);
        }
        layouter.print(")").end();

    }

    public void printABSGetExp(ABSGetExp x) throws IOException {
        x.getChildAt(0).visit(programPrettyPrinter);
        layouter.print(".get");
    }

    public void printABSReturnStatement(ABSReturnStatement x) throws IOException{
        layouter.print("return").brk(1);
        if (x.getChildCount() > 0) {
            layouter.beginC(0);
            x.getChildAt(0).visit(programPrettyPrinter);
            layouter.end();
        }
        layouter.print(";");
    }

    public void printABSMethodFrame(ABSMethodFrame x) throws IOException {
        final boolean fstStmnt = markFirstStatement && x.getStatementCount() == 0;

	if (fstStmnt) {
	    markFirstStatement = false;
	    mark(MARK_START_FIRST_STMT);
	}
	layouter.print("methodframe");
        x.getExecutionContext().visit(programPrettyPrinter);
        layouter.print(":{");
        layouter.beginC(2).ind();
        printStatementList(x);
        layouter.brk(0,-2).end().print("}");
	if (fstStmnt) {
	    markFirstStatement = false;
	    mark(MARK_END_FIRST_STMT);
	}
    }

    public void printABSExecutionContext(ABSExecutionContext x) throws IOException {
        layouter.print("(").beginC(0);
        layouter.print("source <- ");
        x.getMethodLabel().visit(programPrettyPrinter);
        layouter.print(",").ind(1, 0);
        layouter.print("return <- ").print("(").print("var:").ind(1, 0);
        x.getResult().visit(programPrettyPrinter);
        layouter.print(",").ind(1,0).print("fut:").ind(1,0);
        x.getFuture().visit(programPrettyPrinter);
        layouter.end().print(")");
    }


    public void printABSMethodLabel(IABSMethodLabel x) throws IOException {
        layouter.print(x.toString());
    }

}
