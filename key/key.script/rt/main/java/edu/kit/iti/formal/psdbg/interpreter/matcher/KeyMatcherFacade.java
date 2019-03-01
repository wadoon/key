package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import lombok.Builder;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

@Builder
public class KeyMatcherFacade {
    private static Logger logger = LogManager.getLogger(KeyMatcherFacade.class);
    private final DefaultTermParser dtp = new DefaultTermParser();
    private final KeYEnvironment environment;
    private final Sequent sequent;

    private static Logger loggerConsole = LogManager.getLogger("console");

    public Matchings matches(String pattern) {
        Matchings ret;
        if(pattern.contains("==>")) {
            ret = matchesSequent(pattern);
        } else {
            ret = matchesTerm(pattern);
        }
        //loggerConsole.info("Pattern: {} against Sequent: {} matches as {}", pattern, this.sequent, ret);
        return ret;
    }

    private Matchings matchesTerm(String pattern) {
        List<Term> positions = new ArrayList<>();
        for (String patternTerm : hasToplevelComma(pattern)) {
            try {
               Term t = dtp.parse(createReader(patternTerm), null, environment.getServices(),
                       environment.getServices().getNamespaces(), null, true);
               positions.add(t);
            } catch (ParserException e) {
                e.printStackTrace();
            }
        }

        KeyTermMatcher keyTermMatcher = new KeyTermMatcher();
        return keyTermMatcher.matchesToplevel(sequent, positions);
    }


    static List<String> hasToplevelComma(String pattern) {
        ArrayList<String> rt = new ArrayList<>();
        char[] c = pattern.toCharArray();
        int level = 0;
        int lastPosition = 0;
        for (int i = 0; i < c.length; i++) {
            if(c[i]==',' && level==0){
                rt.add(pattern.substring(lastPosition, i));
                lastPosition=i;
            }
            if(c[i]=='(' || c[i]=='{')
                level++;
            if(c[i]==')' || c[i]=='}')
                level--;
        }
        if(rt.isEmpty())
            rt.add(pattern);
        return rt;
    }

    private Matchings matchesSequent(String pattern) {

        Sequent seq = null;
        try {
            seq = dtp.parseSeq(createReader(pattern), environment.getServices(), environment.getServices().getNamespaces(), null,true);
        } catch (ParserException e) {
            e.printStackTrace();
        }
        KeyTermMatcher keyTermMatcher = new KeyTermMatcher();
        return keyTermMatcher.matchesSequent(sequent, seq);
    }

    private Reader createReader(String pattern) {
        StringReader sr = new StringReader(pattern);
        return sr;
    }


}
