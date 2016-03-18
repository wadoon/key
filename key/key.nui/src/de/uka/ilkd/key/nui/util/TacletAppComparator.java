package de.uka.ilkd.key.nui.util;

import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.TacletSchemaVariableCollector;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

// TODO Findbugs wants this class to also implement Serializable. discuss with team.
// FindBugs pattern: Pattern: SE_COMPARATOR_SHOULD_BE_SERIALIZABLE
public class TacletAppComparator implements Comparator<TacletApp> {

    private static int countFormulaSV(TacletSchemaVariableCollector c) {
        int formulaSV = 0;
        Iterator<SchemaVariable> it = c.varIterator();
        while (it.hasNext()) {
            SchemaVariable sv = it.next();
            if (sv instanceof FormulaSV) {
                formulaSV++;
            }
        }

        return formulaSV;
    }

    /** this is a rough estimation about the goal complexity. The
     * complexity depends on the depth of the term to be replaced.
     * If no such term exists we add a constant (may be refined in
     * future)
     */
    private static int measureGoalComplexity(ImmutableList<TacletGoalTemplate> l) {
        int result = 0;
        Iterator<TacletGoalTemplate> it = l.iterator();
        while (it.hasNext()) {
        TacletGoalTemplate gt = it.next();
        if (gt instanceof RewriteTacletGoalTemplate) {
            if (((RewriteTacletGoalTemplate)gt).replaceWith() != null) {
            result += ((RewriteTacletGoalTemplate)gt).replaceWith().depth();
            }
        }
        if (!gt.sequent().isEmpty()) {
            result += 10;
        }
        }
        return result;
    }


    /**
     * rough approximation of the program complexity
     */
    public static int programComplexity(JavaBlock b) {
        if (b.isEmpty()) {
        return 0;
        }
        return new de.uka.ilkd.key.java.visitor.JavaASTWalker(b.program()) {
            private int counter = 0;

            protected void doAction(ProgramElement pe) {
                        counter++;
            }

            public int getCounter() {
            counter = 0;
            start();
            return counter;
            }
        }.getCounter();
    }

    public int compare(TacletApp o1, TacletApp o2) {
            LinkedHashMap<String,Integer> map1 = score(o1);
            LinkedHashMap<String,Integer> map2 = score(o2);
            Iterator<Map.Entry<String,Integer> > it1 = map1.entrySet().iterator();
            Iterator<Map.Entry<String,Integer> > it2 = map2.entrySet().iterator();
            while (it1.hasNext() && it2.hasNext()) {
                String s1 = it1.next().getKey();
                String s2 = it2.next().getKey();
                if (!s1.equals(s2)) throw new IllegalStateException(
                    "A decision should have been made on a higher level ( "+
                    s1+"<->"+s2+")");
                int v1 = map1.get(s1);
                int v2 = map2.get(s2);
                // the order will be reversed when the list is sorted
                if (v1<v2) return 1;
                if (v1>v2) return -1;
            }
            return 0;
    }


        /* A score is a list of named values (comparable lexicographically).
           Smaller value means the taclet should be higher on the list
           offered to the user. Two scores need not contain the same
           named criteria, but the scoring scheme must force a decision
           before the first divergence point.
        */
    public static LinkedHashMap<String,Integer> score(TacletApp o1) {
            LinkedHashMap<String,Integer> map = new LinkedHashMap<String,Integer>();

        final Taclet taclet1 = o1.taclet();

            map.put("closing", taclet1.goalTemplates().size()==0 ? -1:1);

            boolean calc = false;
            for (RuleSet rs : taclet1.getRuleSets()) {
                String s = rs.name().toString();
                if (s.equals("simplify_literals") ||
                    s.equals("concrete") ||
                    s.equals("update_elim") ||
                    s.equals("replace_known_left") ||
                    s.equals("replace_known_right")) calc = true;
            }
            map.put("calc", calc ? -1 : 1);

            int formulaSV1 = 0;
            int cmpVar1 = 0;

        if (taclet1 instanceof FindTaclet) {
                map.put("has_find", -1);

            final Term find1 = ((FindTaclet) taclet1).find();
            int findComplexity1 = find1.depth();
            findComplexity1 += programComplexity(find1.javaBlock());
                map.put("find_complexity", -findComplexity1);

            // depth are equal. Number of schemavariables decides
            TacletSchemaVariableCollector coll1 = new TacletSchemaVariableCollector();
            find1.execPostOrder(coll1);
            formulaSV1 = countFormulaSV(coll1);
            cmpVar1 += -coll1.size();
                map.put("num_sv", -cmpVar1);

        } else {
                map.put("has_find", 1);
        }

            cmpVar1 = cmpVar1-formulaSV1;
            map.put("sans_formula_sv", -cmpVar1);

            map.put("if_seq", taclet1.ifSequent().isEmpty() ? 1 : -1);

            map.put("num_goals", taclet1.goalTemplates().size());

            map.put("goal_compl", measureGoalComplexity(taclet1.goalTemplates()));

            return map;
    }
}
