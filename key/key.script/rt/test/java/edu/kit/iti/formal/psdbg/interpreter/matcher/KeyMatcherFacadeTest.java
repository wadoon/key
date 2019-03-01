package edu.kit.iti.formal.psdbg.interpreter.matcher;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.Reader;
import java.io.StringReader;

public class KeyMatcherFacadeTest {

    private final static DefaultTermParser dtp = new DefaultTermParser();
    private Services services;
    private AbbrevMap abbrev;
    private NamespaceSet namespace;
    private KeYEnvironment keyenv;


    @Before
    public void loadKeyEnv() throws ProblemLoaderException {
        String file = getClass().getResource("test.key").toExternalForm().substring(5);

        KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(new File(file));
        keyenv = env;
        services = env.getServices();
        namespace = env.getServices().getNamespaces();
        abbrev = new AbbrevMap();

    }


    /**
     * Actually testcases for KeyTermMatcher not for Facade
     * @throws Exception
     */
    @Test
    public void matchTerms() throws Exception {
        System.out.println(shouldMatchT("f(a)", "?"));
        System.out.println(shouldMatchT("f(a)", "f(a)"));

        shouldMatchT("f(a)", "?X", "[{?X=f(a)}]");
        shouldMatchT("h(a,a)", "h(?X,?X)", "[{?X=a}]");

    }


    @Test
    public void matchSeq() throws Exception {
       //atm missing is catching the toplevel formula
        shouldMatch("!q==>p,!p","!q ==> p", "[{}]");
        shouldMatch("!p ,p ==> q", "!p ==> q", "[{}]");
        shouldMatch("!q ,p ==> q", "!p ==> q", "{NOMATCH}");
        shouldMatch("!q==>p,!p","!q ==> p", "[{}]");
        shouldMatch("!p ,p ==> q", "!p ==> q", "[{}]");
        shouldMatch("!q ,p ==> q", "!p ==> q", "{NOMATCH}");



        shouldMatch(" ==> !p, p,!q", "==> ?Z, !(?Z)", "[{?Z=p}]");

        shouldMatch("==> pred(a)", "==> pred(?)");
        shouldMatch("p, q ==> !p, !q", "==> ?Z", "[{?Z=not(p)}, {?Z=not(q)}]");
        shouldMatch("2 >= 1, h2(1,2) = h2(2,3), h2(2,3) = 0 ==> p, !p", "?X=0 ==>", "[{?X=h2(Z(2(#)),Z(3(#)))}]");
        shouldMatch("h2(2,2) = 0 ==>p, !p", "?X=0 ==>", "[{?X=h2(Z(2(#)),Z(2(#)))}]");
        shouldMatch("p ==>", "p ==>", "[{}]");
        shouldMatch("==> pred(a), q", "==> pred(?X:S), q", "[{?X=a}]");
        shouldMatch("==> p, q", "==> ?X:Formula", "[{?X=p}, {?X=q}]");
        shouldMatch("==> p, q", "==> p, q","[{}]");
        shouldMatch("==> p, q", "==> q, p", "[{}]");
        shouldMatch("==> pred(a), q", "==> pred(?X)", "[{?X=a}]");
        shouldMatch("h2(2,2) = 0 ==>", "?X=0 ==>", "[{?X=h2(Z(2(#)),Z(2(#)))}]");
        shouldMatch("==>f(g(a))= 0", "==> f(...a...) = 0", "[{}]");


    }

    @Test
    public void negativeMatchSeq() throws Exception {
        shouldNotMatch("p==>", "==> p");

    }

    @Test
    public void testBindContext() throws Exception {
        //how to deal with trying to match top-level, w.o. adding the type of the variable
        shouldMatch("f(a)=0 ==> ", "(f(a)=0) : ?Y:Formula ==>", "[{?Y=equals(f(a),Z(0(#)))}]");
        //shouldMatch("f(g(a))", "_ \\as ?Y", "[{?Y=f(g(a))}]");
        shouldMatchT("i+i+j", "(?X + ?Y) : ?Z", "[{?X=add(i,i), ?Y=j, ?Z=add(add(i,i),j)}]");


        shouldMatch("==>f(g(a))= 0", "==> f((...a...):?G) = 0", "[{?G=g(a)}]");
        shouldMatch("==>f(f(g(a)))= 0", "==> f((...a...):?G) = 0", "[{?G=f(g(a))}]");
        shouldMatch("==>f(f(g(a)))= 0", "==> f((...g(...a...)...):?G) = 0", "[{?G=f(g(a))}]");
        shouldMatch("==>f(f(g(a)))= 0", "==> f((...g((...a...):?Q)...):?G) = 0", "[{?G=f(g(a)), ?Q=a}]");
        shouldMatch("pred(f(a)) ==>", "pred((...a...):?Q) ==>","[{?Q=f(a)}]");
        shouldMatch("p ==>", "(p):?X:Formula ==>", "[{?X=p}]");
        shouldMatch("pred(a) ==>", "(pred(?)):?X:Formula ==>");
        shouldMatch("==>f(f(g(a)))= 0", "==> ((f((...g((...a...):?Q)...):?G)):?R):?Y = 0", "[{?G=f(g(a)), ?Q=a, ?R=f(f(g(a))), ?Y=f(f(g(a)))}]");

    }

    @Test
    public void testQuantMatch() throws Exception {
        shouldMatch("\\forall int x; fint2(1,x) ==>", "\\forall ?X; (...?X...)", "[{?X=x}]");

        shouldMatch("\\forall int x; fint2(1,x) ==>", "\\forall ?X; fint2(1,?X)", "[{?X=x}]");
        shouldMatch("\\forall int x; fint2(1,x) ==>", "\\forall ?X; ?"); //"[{?X=x:int}]"

        shouldMatchT("fint2(1,i)", "fint2(1,i)", "[{}]");

        shouldMatch("\\exists int i, int j; fint2(j,i) ==> ", "(\\exists ?Y, ?X; ?Term) ==> ", "[{?Term=fint2(j,i), ?X=j:int, ?Y=i:int}]");

//        shouldMatchForm("\\exists int i; fint2(1,i)", "(\\exists ?X _)");
//        shouldMatchForm("\\exists int i; fint2(1,i)", "(\\exists ?X (fint2(1,?X)))");

        shouldMatch("\\exists int j; fint2(j,i) ==>", "(\\exists int j; ?X)==>", "[{?X=fint2(j,i)}]");

        shouldMatch("\\forall int i; \\exists int j; fint2(j,i) ==>", "(\\forall int i; (\\exists int j; fint2(i,j)))==>", "{NOMATCH}");

    }

    @Test
    public void hasToplevelComma() throws Exception {
        Assert.assertTrue(!KeyMatcherFacade.hasToplevelComma("a=b,c=d").isEmpty());
        Assert.assertFalse(KeyMatcherFacade.hasToplevelComma("f(a,b)").isEmpty());
    }


    //region: helper

    private void shouldNotMatch(String s, String s1) throws Exception{
        Assert.assertTrue(shouldMatch(s, s1).getMatchings().size()==0);
    }

    private void shouldMatch(String keysequent, String pattern, String exp) throws Exception {

        Matchings m = shouldMatch(keysequent, pattern);
        System.out.println("m = " + m);
        Assert.assertEquals(exp, m.toString());

    }

    private Matchings shouldMatch(String keysequent, String pattern) throws ParserException {
        Sequent seq = parseKeySeq(keysequent);
        KeyMatcherFacade.KeyMatcherFacadeBuilder builder = KeyMatcherFacade.builder().environment(keyenv);
        KeyMatcherFacade kfm = builder.sequent(seq).build();
        return kfm.matches(pattern);

    }

    private Matchings shouldMatchT(String keyterm, String pattern) throws ParserException {
        KeyTermMatcher ktm = new KeyTermMatcher();
        Matchings m = ktm.visit(parseKeyTerm(pattern), MatchPathFacade.createRoot(parseKeyTerm(keyterm)));
        return  m;

    }

    private void shouldMatchT(String s, String s1, String exp) throws ParserException {
        Matchings m = shouldMatchT(s, s1);
        System.out.println("m = " + m);
        Assert.assertEquals(m.toString(), exp);
    }

    public Sequent parseKeySeq(String seq) throws ParserException {
        Reader in = new StringReader(seq);
        return dtp.parseSeq(in, services, namespace, abbrev);
    }

    public Term parseKeyTerm(String t) throws ParserException {
        Reader in = new StringReader(t);
        return dtp.parse(in, null, services, namespace, abbrev, true);
    }

    //endregion


}