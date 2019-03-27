package edu.kit.iti.formal.psdbg.interpreter.matcher;

import com.google.common.collect.Sets;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import lombok.Getter;
import lombok.Setter;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class KeyTermMatcher extends  KeyTermBaseVisitor<Matchings, MatchPath> {
    Random random = new Random(42L);

   // MatchPath peek;
    private List<Integer> currentposition = new ArrayList<>();

    @Setter @Getter private boolean catchAll = false;
    @Setter
    java.util.function.BiFunction<QuantifiableVariable, Term, Term> parseQuantVar;


    public Matchings matchesToplevel(Sequent sequent, List<Term> patternTerms) {
        MatchPath.MPSequent seq = MatchPathFacade.create(sequent);

        Matchings ret = new MutableMatchings();
        Matchings antecMatches = matchesSemisequent(MatchPathFacade.createAntecedent(seq), patternTerms);
        Matchings succMatches = matchesSemisequent(MatchPathFacade.createSuccedent(seq), patternTerms);

        //if(!antecMatches.equals(EmptyMatch.INSTANCE))
        ret.addAll(antecMatches);
        //if(!succMatches.equals(EmptyMatch.INSTANCE))
        ret.addAll(succMatches);
        return ret;
    }


    public Matchings matchesSequent(Sequent sequent, Sequent pattern) {
        MatchPath.MPSequent mps = MatchPathFacade.create(sequent);
        MatchPath.MPSemiSequent succPath = MatchPathFacade.createSuccedent(mps);
        Matchings ms = matchesSemisequent(succPath, pattern.succedent());
        Matchings ma = matchesSemisequent(MatchPathFacade.createAntecedent(mps), pattern.antecedent());
        return ms.reduceConform(ma);
    }

    private Matchings matchesSemisequent(MatchPath.MPSemiSequent peek, Semisequent pattern) {
        List<Term> patterns = pattern.asList().stream().map(SequentFormula::formula).collect(Collectors.toList());
        return matchesSemisequent(peek, patterns);
    }


    private Matchings matchesSemisequent(MatchPath.MPSemiSequent peek, List<Term> patterns) {

        Semisequent semiSeq = peek.getUnit();

        if (semiSeq.isEmpty()) {
            if(patterns.isEmpty()){
                return MutableMatchings.emptySingleton();
            } else {
                return NoMatch.INSTANCE;
                //return new MutableMatchings();
            }
        }
        if(!semiSeq.isEmpty() && patterns.isEmpty()){
            return MutableMatchings.emptySingleton();
        }
        HashMap<Term, Map<SequentFormula, Matchings>> map = new HashMap<>();
        List<MatchPath.MPSequentFormula> sequentFormulas =
                IntStream.range(0, semiSeq.size())
                        .mapToObj(pos -> MatchPathFacade.create(peek, pos))
                        .collect(Collectors.toList());

        //cartesic product of pattern and top-level terms
        for (Term subPatternTerm : patterns) {
            map.put(subPatternTerm, new HashMap<>());
            for (MatchPath.MPSequentFormula sf : sequentFormulas) {
                Matchings temp = visit(subPatternTerm, MatchPathFacade.create(sf));
                if (!temp.isNoMatch())
                    map.get(subPatternTerm).put(sf.getUnit(), temp);
            }
        }

        List<Matchings> matchings = new ArrayList<>();
        reduceDisjoint(map, patterns, matchings);

        if (map.values().stream().allMatch(Map::isEmpty))
            return NoMatch.INSTANCE;

        Matchings ret = new MutableMatchings();
        //.filter(x -> !x.equals(EmptyMatch.INSTANCE))
        matchings.forEach(ret::addAll);
        return ret;
    }


    /**
     * Visit a '...'MatchPath'...' structure
     * @param pattern
     * @param subject
     * @return
     */
    @DispatchOn(EllipsisOp.class)
    public Matchings visitEllipsisOp(Term pattern, MatchPath subject) {
        Matchings matchings = new MutableMatchings();
        
        subTerms((MatchPath.MPTerm) subject).forEach(sub -> {
            Matchings s = visit(pattern.sub(0), sub);
            matchings.addAll(s);
        });
        return matchings;
    }


    /**
     * Visit a MatchIdentifierOP e.g., ?X or ?
     * @param pattern
     * @param subject
     * @return
     */
    @DispatchOn(MatchIdentifierOp.class)
    public Matchings visitMatchIdentifierOp(Term pattern, MatchPath subject) {
        if(subject != null) {
            String name = pattern.op().name().toString();
            if (name.equalsIgnoreCase("?")) {
                name = getRandomName();
            }
            Matchings mSingleton = MutableMatchings.singleton(name, subject);
            return mSingleton;
        } else {
            return NoMatch.INSTANCE;
        }

    }


    @DispatchOn(Quantifier.class)
    public Matchings visitQuantifier(Term pattern, MatchPath subject) {
        Term toMatch = (Term) subject.getUnit();
        if (!toMatch.op().equals(pattern.op())) {
            return NoMatch.INSTANCE;
        }
        // Decision: Order of bounded vars
        if (toMatch.boundVars().size() != pattern.boundVars().size()) {
            return NoMatch.INSTANCE;
        }
        Matchings mm = new MutableMatchings();

        Match mPaths = new Match();
        mm.add(mPaths);

        for (int i = 0; i < toMatch.boundVars().size(); i++) {
            QuantifiableVariable bv = toMatch.boundVars().get(i);
            QuantifiableVariable pv = pattern.boundVars().get(i);

            if (pv instanceof MatchIdentifierOp) {
                //Namensbehandlung
                String name;
                if (pv.name().toString().equalsIgnoreCase("?")) {
                    name = getRandomName();
                } else {
                    name = pv.name().toString();
                }
                MatchPath mp = new MatchPath.MPQuantifiableVariable(subject, bv, -i);
                mPaths.put(name, mp);
//                mPaths.put(name, subject);
            } else if (!pv.name().equals(bv.name())) {
                return NoMatch.INSTANCE;
            }
        }

        Term scope = toMatch.sub(0);
        Matchings m = visit(pattern.sub(0), MatchPathFacade.create(subject, 0));
        mm = m.reduceConform(mm);
        return mm;
//      return null;

    }

    @DispatchOn(MatchBinderOp.class)
    public Matchings visitMatchBinderOp(Term pattern, MatchPath subject) {
        Matchings matchings = visit(pattern.sub(1), subject);
        if (matchings != NoMatch.INSTANCE) {
            String name = pattern.sub(0).op().name().toString();
            for (Match a : matchings.getMatchings()) {
                a.put(name, subject);
            }
        }
        return matchings;
    }



    @Override
    protected Matchings defaultVisit(Term pattern, MatchPath subject1) {
        Matchings m = MutableMatchings.emptySingleton();
        //Matchings m = new MutableMatchings();
        MatchPath<Term, Object> subject = (MatchPath<Term, Object>) subject1;
        if (subject.getUnit().subs().size() != pattern.subs().size()) {
            return NoMatch.INSTANCE;
        }
      //  if(pattern.equals(subject1.getUnit()))
      //      return EmptyMatch.INSTANCE;
            // return Matchings.singleton(pattern.toString(), subject1);
//       if(pattern.op().equals(((Term) subject1.getUnit()).op())) {
        if(pattern.op().name().equals(((Term) subject1.getUnit()).op().name())) {
            for (int i = 0; i < subject.getUnit().subs().size(); i++) {
               Term tt = subject.getUnit().sub(i);
               Term pt = pattern.sub(i);
               Matchings msub = visit(pt, MatchPathFacade.create(subject, i));

               if (msub.equals(NoMatch.INSTANCE)) {
                   return NoMatch.INSTANCE;
               }
               m = m.reduceConform(msub);
           }
       } else {
            return NoMatch.INSTANCE;
       }

        return m;
    }

    //region helper

    public String getRandomName() {
        return "??_" + getRandomNumber();
    }

    private int getRandomNumber() {
        return Math.abs(random.nextInt());
    }

    private Stream<MatchPath.MPTerm> subTerms(MatchPath.MPTerm peek) {
        ArrayList<MatchPath.MPTerm> list = new ArrayList<>();
        subTerms(list, peek);
        return list.stream();
    }

    private void subTerms(ArrayList<MatchPath.MPTerm> list, MatchPath.MPTerm peek) {
        list.add(peek);
        for (int i = 0; i < peek.getUnit().arity(); i++) {
            subTerms(list, MatchPathFacade.create(peek, i));
        }
    }
    //endregion

    //region Reductions



    /* @param map
     * @param patterns
     * @param matchings
     */
    private void reduceDisjoint(HashMap<Term, Map<SequentFormula, Matchings>> map,
                                List<Term> patterns,
                                List<Matchings> matchings) {
        reduceDisjoint(map, patterns, matchings, 0, MutableMatchings.emptySingleton(), new HashSet<>());
    }

    /**
     * @param map
     * @param patterns
     * @param matchings
     * @param currentPatternPos
     * @param ret
     * @param chosenSequentFormulas
     */
    private void reduceDisjoint(HashMap<Term, Map<SequentFormula, Matchings>> map,
                                List<Term> patterns,
                                List<Matchings> matchings,
                                int currentPatternPos,
                                Matchings ret,
                                Set<SequentFormula> chosenSequentFormulas) {
        if (currentPatternPos >= patterns.size()) { // end of selection process is reached
            matchings.add(ret);
            return;
        }

        Term currentPattern = patterns.get(currentPatternPos);
        Sets.SetView<SequentFormula> topLevelFormulas =
                Sets.difference(map.get(currentPattern).keySet(), chosenSequentFormulas);

        if (topLevelFormulas.size() == 0) {
            return; // all top level formulas has been chosen, we have no matches left
        }

        for (SequentFormula formula : topLevelFormulas) { // chose a toplevel formula
            // the matchings for current pattern against the toplevel
            Matchings m = map.get(currentPattern).get(formula);
            //join them with the current Matchings
            Matchings mm = m.reduceConform(ret);
            chosenSequentFormulas.add(formula); // adding the formula, so other matchings can not choose it

            // recursion: choose the next matchings for the next pattern
            reduceDisjoint(map, patterns, matchings,
                    currentPatternPos + 1, mm, chosenSequentFormulas);

            chosenSequentFormulas.remove(formula); // delete the formula, so it is free to choose, again
        }
    }


//endregion

}
