package de.uka.ilkd.key.rule.join;

import java.util.LinkedHashMap;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ContainsStatementVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstraction;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

public class JoinPointRule implements BuiltInRule {
    public static final JoinPointRule INSTANCE = new JoinPointRule();

    private static final String DISPLAY_NAME = "Join Point";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public JoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        PosInOccurrence pio = ruleApp.posInOccurrence();
        JoinRuleBuiltInRuleApp app = new JoinRuleBuiltInRuleApp(new JoinRule(),
                pio);

        StatementBlock block = (StatementBlock) JoinRuleUtils
                .getJavaBlockRecursive(pio.subTerm()).program();

        JoinPointStatement jPS = ((JoinPointStatement) block
                .getInnerMostMethodFrame().getBody().getFirstElement());

        Pair<JoinProcedure, String> specs = services
                .getSpecificationRepository().getMergeSpecs(jPS);
        JoinProcedure concreteRule = specs.first;
        String params = specs.second;

        if (concreteRule.toString().equals("JoinByPredicateAbstraction")) {
            concreteRule = getProcedure(params, concreteRule, services);
        }

        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                .findPotentialJoinPartners(goal, pio, goal.proof().root());

        app.setJoinNode(goal.node());
        app.setConcreteRule(concreteRule);
        app.setJoinPartners(joinPartners);

        ImmutableList<Goal> newGoals = goal.split(1);
        Goal g = newGoals.head();
        newGoals = g.apply(app);

        return newGoals;
    }

    private JoinWithPredicateAbstraction getProcedure(String params,
            JoinProcedure joinProc, Services services) {
        Class<? extends AbstractPredicateAbstractionLattice> latticeType = null;
        List<AbstractionPredicate> predicates = null;
        Pattern p = Pattern.compile("([a-z]+)\\s*\\((.+?)\\)");
        Matcher m = p.matcher(params);
        while (m.find()) {
            if (m.group(1).equals("rep")) {

                URL path = JMLSpecFactory.class.getResource("domains.txt");
                String line = "";
                File f = new File(path.getFile());
                boolean found = false;
                try (BufferedReader br = new BufferedReader(
                        new FileReader(f))) {
                    while ((line = br.readLine()) != null && !found) {
                        String[] content = line.split(",", 3);
                        if (m.group(2).equals(content[0])) {
                            found = true;
                            latticeType = translateLatticeType(content[1]);
                            predicates = getPredicates(content[2], services);
                        }
                    }
                }
                catch (IOException e) {

                }

            }
            else {
                latticeType = translateLatticeType(m.group(1));
                predicates = getPredicates(m.group(2), services);
            }
        }
        final JoinWithPredicateAbstractionFactory absPredicateFactory = (JoinWithPredicateAbstractionFactory) joinProc;
        return absPredicateFactory.instantiate(predicates, latticeType,
                new LinkedHashMap<ProgramVariable, AbstractDomainElement>());
    }

    private Class<? extends AbstractPredicateAbstractionLattice> translateLatticeType(
            String type) {
        if (type.equals("simple"))
            return SimplePredicateAbstractionLattice.class;
        else if (type.equals("conjunctive"))
            return ConjunctivePredicateAbstractionLattice.class;
        else if (type.equals("disjunctive"))
            return DisjunctivePredicateAbstractionLattice.class;
        else
            return null;
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()
                && !goal.isLinked()
                && JavaTools.getActiveStatement(
                        TermBuilder.goBelowUpdates(pio.subTerm())
                                .javaBlock()) instanceof JoinPointStatement) {

            JoinPointStatement jPS = (JoinPointStatement) JavaTools
                    .getActiveStatement(TermBuilder
                            .goBelowUpdates(pio.subTerm()).javaBlock());
            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                    .findPotentialJoinPartners(goal, pio);
            Pair<JoinProcedure, String> specs = goal.node().proof()
                    .getServices().getSpecificationRepository()
                    .getMergeSpecs(jPS);
            JoinProcedure joinProc = specs.first;
            String params = specs.second;

            if (!joinPartners.isEmpty() && (!joinProc.toString()
                    .equals("JoinByPredicateAbstraction")
                    || !hasCorrectParams(params, goal.proof().getServices()))) {

                ImmutableList<Goal> joinPartnersGoal = ImmutableSLList.nil();

                for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                    joinPartnersGoal = joinPartnersGoal.append(p.first);
                }

                ImmutableList<Goal> openGoals = goal.node().proof().openGoals();
                for (Goal g : openGoals) {
                    if (!g.equals(goal) && !g.isLinked()
                            && !joinPartnersGoal.contains(g)
                            && containsJPS(g, jPS)) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }

    public static boolean containsJPS(Goal g, JoinPointStatement jPS) {
        Services services = g.proof().getServices();
        Term t;
        Semisequent sequent = g.node().sequent().succedent();
        for (int i = 0; i < g.node().sequent().succedent().size(); i++) {
            t = sequent.get(i).formula();
            MethodFrame mF = JavaTools.getInnermostMethodFrame(
                    JoinRuleUtils.getJavaBlockRecursive(t), services);
            if(mF != null){
            ContainsStatementVisitor visitor = new ContainsStatementVisitor(mF,
                    jPS, services);
           visitor.start();
           if(visitor.isContained()) return true;
            }
        }
        return false;
    }


    private boolean hasCorrectParams(String params, Services services) {
        /* params string  = latticeType(...)
         * Matcher separates the string in m.group(1) = laticeType
         * m.group(2) = string contained between the parenthesis
         */
        
        Pattern p = Pattern.compile("([a-z]+)\\s*\\((.+?)\\)");
        Matcher m = p.matcher(params);
        boolean matched = false;

        while (m.find()) {
            matched = true;
            if (m.groupCount() != 2)
                return false;
            else {
                List<AbstractionPredicate> predicates = getPredicates(
                        m.group(2), services);
                if (((m.group(1).equals("conjunctive")
                        || m.group(1).equals("disjunctive")
                        || m.group(1).equals("simple")) && predicates.isEmpty())
                        || !m.group(1).equals("rep"))
                    return false;
            }
        }
        return matched;
    }

    private List<AbstractionPredicate> getPredicates(String predicatesStr,
            Services services) {
        List<AbstractionPredicate> result = new ArrayList<AbstractionPredicate>();
        /* parameters string should have the following structure
        * placeholder -> {predicate, predicate1, ...} (whitespaces are optional)
        * m.group(1) = placeholder and m.group(2) = all the predicates
        * Placeholder structure: SORT var (NOTE: space between the sort and the variable is obligatory) 
        * Example: int x 
        */
        Pattern p = Pattern.compile("(.+?)\\s*->\\s*\\{(.+?)\\}");
        Matcher m = p.matcher(predicatesStr);
        while (m.find()) {
            if (m.groupCount() != 2) {
                result.clear();
                break;
            }
            else {
                try {
                    final String phStr = m.group(1);
                    Pair<Sort, Name> ph = null;
                    ph = JoinRuleUtils.parsePlaceholder(phStr, false, services);
                    if (services.getNamespaces().variables()
                            .lookup(ph.second) == null) {
                        services.getNamespaces().variables()
                                .add(new LocationVariable(
                                        new ProgramElementName(
                                                ph.second.toString()),
                                        ph.first));
                    }

                    ArrayList<Pair<Sort, Name>> phList = JoinRuleUtils
                            .singletonArrayList(ph);
                    // it separates the predicates by a comma.
                    // Example: for input "x>=0, x<=10", m.groupCount=1
                    // 1.m.find() -> m.group(1) = m.group(0) = "x>=0"
                    // 2.m.find() -> m.group(1) = m.group(0) = "x<=10"
                    Pattern p1 = Pattern.compile("([^,]+)");
                    Matcher m1 = p1.matcher(m.group(2));
                    while (m1.find()) {
                        result.add(JoinRuleUtils.parsePredicate(m1.group(0),
                                phList, services));
                    }
                }
                catch (ParserException
                        | JoinRuleUtils.SortNotKnownException e) {
                    result.clear();
                }
            }
        }
        return result;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new JoinPointBuiltInRuleApp(this, pos);
    }

}
