package de.uka.ilkd.key.rule.join;

import java.util.LinkedHashMap;
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
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.JoinPointStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.intermediate.BuiltInAppIntermediate;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.join.procedures.JoinWithPredicateAbstractionFactory;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.SimpleBlockContract;
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

        JoinProcedure concreteRule = jPS.getJoinProc();
        // TODO: set joinParams;

        if (concreteRule.toString().equals("JoinByPredicateAbstraction")) {
            concreteRule = predAbstrWithParameters(concreteRule,
                    jPS.getContract().getJoinParams(), services);
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

    private JoinProcedure predAbstrWithParameters(JoinProcedure joinProc,
            String joinParams, Services services) {
        if (joinParams.isEmpty()) {
            return null;
        }

        Pattern p = Pattern.compile("([^\"]+) : ([^\"]+)");
        Matcher m = p.matcher(joinParams);

        if (m.find()) {
            Class<? extends AbstractPredicateAbstractionLattice> latticeType = translateLatticeType(
                    m.group(1));

            List<AbstractionPredicate> predicates = null;
            predicates = getPredicates(m.group(2), services);
           
            final JoinWithPredicateAbstractionFactory absPredicateFactory = (JoinWithPredicateAbstractionFactory) joinProc;
            joinProc = absPredicateFactory.instantiate(predicates, latticeType,
                    new LinkedHashMap<ProgramVariable, AbstractDomainElement>());
        }
        else {
           return null;
        }
        return joinProc;
    }

    private Class<? extends AbstractPredicateAbstractionLattice> translateLatticeType(
            String type) {
        if (type.equals("simple"))
            return SimplePredicateAbstractionLattice.class;
        else if (type.equals("con"))
            return ConjunctivePredicateAbstractionLattice.class;
        else if (type.equals("dis"))
            return DisjunctivePredicateAbstractionLattice.class;
        else
            return null;
    }
    
    private List<AbstractionPredicate> getPredicates(String input, Services services){
        final ArrayList<AbstractionPredicate> result =
                new ArrayList<AbstractionPredicate>();
        Pattern p = Pattern.compile("\\('(.+?)', '(.+?)'\\)");
        Matcher m = p.matcher(input);
        //Report Error?
        boolean matched = false;
        while (m.find()) {
            matched = true;

            for (int i = 1; i < m.groupCount(); i += 2) {
                
                final String phStr = m.group(i);
                final String predStr = m.group(i + 1);
                String[] preds = predStr.split("', '");

                // Parse the placeholder
                Pair<Sort, Name> ph = null;
                ph = JoinRuleUtils.parsePlaceholder(phStr, false, services);

                // Add placeholder to namespaces, if necessary
                if (services.getNamespaces().variables().lookup(ph.second) == null) {
                    services.getNamespaces()
                            .variables()
                            .add(new LocationVariable(new ProgramElementName(
                                    ph.second.toString()), ph.first));
                }
                for(int j = 0; j < preds.length; j++){
                    try {
                        result.add(JoinRuleUtils.parsePredicate(preds[j],
                                JoinRuleUtils.singletonArrayList(ph), services));
                    }
                    catch (ParserException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                }
            }
        }
        return result;
        
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
                && !goal.isLinked()) {

            SourceElement st = JavaTools.getActiveStatement(
                    TermBuilder.goBelowUpdates(pio.subTerm()).javaBlock());

            if (st instanceof JoinPointStatement) {

                BlockContract contract = ((JoinPointStatement) st)
                        .getContract();

                ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                        .findPotentialJoinPartners(goal, pio);

                if (!joinPartners.isEmpty()) {

                    ImmutableList<Goal> joinPartnersGoal = ImmutableSLList
                            .nil();

                    for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                        joinPartnersGoal = joinPartnersGoal.append(p.first);
                    }

                    ImmutableList<Goal> openGoals = goal.node().proof()
                            .openGoals();
                    
                    for (Goal g : openGoals) {
                        // not linked
                        if (!g.equals(goal) && !g.isLinked()
                                && !joinPartnersGoal.contains(g)) {

                            if (hasSameBlockContractRule(g, contract))
                                return false;

                            JavaBlock jB;
                            for (int i = 0; i < g.node().sequent().succedent()
                                    .size(); i++) {
                                jB = JoinRuleUtils.getJavaBlockRecursive(
                                        g.node().sequent().succedent().get(i)
                                                .formula());
                                MethodFrame mF = JavaTools
                                        .getInnermostMethodFrame(jB,
                                                goal.proof().getServices());
                                if (mF != null && hasSameBlock(mF.getBody(),
                                        contract.getBlock())) {

                                    return false;
                                }
                            }

                        }
                    }
                    
                    return checkParameters(goal, pio,(JoinPointStatement) st) != null;
                }
            }
        }

        return false;
    }

    private JoinProcedure checkParameters(Goal goal, PosInOccurrence pio, JoinPointStatement st) {
      
        JoinProcedure concreteRule = st.getJoinProc();
      
        if (concreteRule.toString().equals("JoinByPredicateAbstraction") ) {
            concreteRule = predAbstrWithParameters(concreteRule,
                    st.getContract().getJoinParams(), goal.node().proof().getServices());
        }
        
        return concreteRule;

        
    }

    private boolean hasSameBlockContractRule(Goal g, BlockContract contract) {
        for (RuleApp rA : g.appliedRuleApps()) {
            if (rA instanceof BlockContractBuiltInRuleApp
                    && ((BlockContractBuiltInRuleApp) rA).getContract()
                            .equals(contract))
                return true;
        }
        return false;
    }

    // TODO: test more complex cases
    private boolean hasSameBlock(StatementBlock block1, StatementBlock block2) {
        boolean result = false;
        ProgramElement pE;
        for (int i = 0; i < block1.getChildCount() && !result; i++) {
            pE = block1.getChildAt(i);
            result = (pE instanceof StatementBlock) ? (pE.equals(block2)) ? true
                    : hasSameBlock((StatementBlock) pE, block2) : false;
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
