package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import lombok.Builder;
import org.slf4j.LoggerFactory;
import org.slf4j.Logger;

import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;

@Builder
public class KeyMatcherFacade {
    private static Logger logger = LoggerFactory.getLogger(KeyMatcherFacade.class);
    private static Logger loggerConsole = LoggerFactory.getLogger("console");
    private final DefaultTermParser dtp = new DefaultTermParser();
    private final Services services;
    private final Sequent sequent;

    static List<String> hasToplevelComma(String pattern) {
        ArrayList<String> rt = new ArrayList<>();
        char[] c = pattern.toCharArray();
        int level = 0;
        int lastPosition = 0;
        for (int i = 0; i < c.length; i++) {
            if (c[i] == ',' && level == 0) {
                rt.add(pattern.substring(lastPosition, i));
                lastPosition = i;
            }
            if (c[i] == '(' || c[i] == '{')
                level++;
            if (c[i] == ')' || c[i] == '}')
                level--;
        }
        if (rt.isEmpty())
            rt.add(pattern);
        return rt;
    }

    public Matchings matches(String pattern) {
        Matchings ret;
        if (pattern.contains("==>")) {
            ret = matchesSequent(pattern);
        } else {
            ret = matchesTerm(pattern);
        }
        //loggerConsole.info("Pattern: {} against Sequent: {} matches as {}", pattern, this.sequent, ret);
        return ret;
    }

    public Matchings matchesTerm(String pattern) {
        List<Term> positions = new ArrayList<>();
        for (String patternTerm : hasToplevelComma(pattern)) {
            try {
                Term t = dtp.parse(createReader(patternTerm), null, services, services.getNamespaces(), null, true);
                positions.add(t);
            } catch (ParserException e) {
                e.printStackTrace();
            }
        }

        KeyTermMatcher keyTermMatcher = new KeyTermMatcher();
        return keyTermMatcher.matchesToplevel(sequent, positions);
    }

    private Matchings matchesSequent(String pattern) {
        Sequent seq = null;
        try {
            seq = dtp.parseSeq(createReader(pattern), services, services.getNamespaces(), null, true);
        } catch (ParserException e) {
            e.printStackTrace();
        }
        KeyTermMatcher keyTermMatcher = new KeyTermMatcher();
        return keyTermMatcher.matchesSequent(sequent, seq);
    }

    private static Reader createReader(String pattern) {
        return new StringReader(pattern);
    }


    public static boolean matchesTerm(Services services, String pattern, Term term) throws ParserException {
        List<Term> positions = new ArrayList<>();
        Term termPattern = new DefaultTermParser().parse(createReader(pattern),
                null, services, services.getNamespaces(),
                null, true);
        KeyTermMatcher keyTermMatcher = new KeyTermMatcher();
        Matchings m = keyTermMatcher.matchesTerm(termPattern, term);
        return !m.isNoMatch();
    }
}
