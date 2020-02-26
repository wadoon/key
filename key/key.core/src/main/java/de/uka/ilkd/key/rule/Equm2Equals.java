package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;

/**
 * @author Alexander Weigl
 * @version 1 (2/26/20)
 */
public class Equm2Equals {
    private RewriteTaclet base;
    private Name name = new Name("equm2equals");

    public static void register(InitConfig initConfig) {
        Taclet t = getTacletObj(initConfig);
        System.out.println(t);
        initConfig.registerRule(t, AxiomJustification.INSTANCE);
        initConfig.setTaclets(initConfig.getTaclets().prepend(t));

        t = getTacletStr(initConfig);
        System.out.println(t);
        initConfig.registerRule(t, AxiomJustification.INSTANCE);
        initConfig.setTaclets(initConfig.getTaclets().prepend(t));
    }

    private static Taclet getTacletObj(InitConfig initConfig) {
        Services services = initConfig.getServices();
        RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        TermBuilder TB = services.getTermBuilder();
        TermFactory TF = services.getTermFactory();
        Named equm = services.getNamespaces().lookup(new Name("equm"));
        assert equm != null;
        tb.setName(new Name("equm2equals"));
        Sort sortObj = services.getNamespaces().sorts().lookup("java.lang.Object");
        TermSV svp1 = SchemaVariableFactory.createTermSV(new Name("p1"), sortObj, false, false);
        TermSV svp2 = SchemaVariableFactory.createTermSV(new Name("p1"), sortObj, false, false);
        Term p1 = TB.var(svp1), p2 = TB.var(svp2);
        tb.setFind(TB.func((Function) equm, p1, p2));
        ProgramMethod equals = (ProgramMethod) services.getNamespaces().lookup(
                new Name("java.lang.Object::equals"));
        Term callEquals= TF.createTerm(equals, TB.getBaseHeap(), p1, p2);
        tb.addGoalTerm(TB.equals(callEquals, TB.TRUE()));

        final RewriteTaclet rewriteTaclet = tb.getRewriteTaclet();
        initConfig.getTaclet2Builder().put(rewriteTaclet, tb);
        return rewriteTaclet;
    }

    private static Taclet getTacletStr(InitConfig initConfig) {
        Services services = initConfig.getServices();
        RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        TermBuilder TB = services.getTermBuilder();
        TermFactory TF = services.getTermFactory();
        Named equm = services.getNamespaces().lookup(new Name("equm"));
        assert equm != null;
        tb.setName(new Name("equm4str"));
        Sort sortObj = services.getNamespaces().sorts().lookup("java.lang.String");
        TermSV svp1 = SchemaVariableFactory.createTermSV(new Name("p1"), sortObj, false, false);
        TermSV svp2 = SchemaVariableFactory.createTermSV(new Name("p2"), sortObj, false, false);
        Term p1 = TB.var(svp1), p2 = TB.var(svp2);
        tb.setFind(TB.func((Function) equm, p1, p2));
        ProgramMethod equals = (ProgramMethod) services.getNamespaces().lookup(
                new Name("java.lang.String::equals"));
        Term callEquals= TF.createTerm(equals, TB.getBaseHeap(), p1, p2);
        tb.addGoalTerm(TB.equals(callEquals, TB.TRUE()));

        final RewriteTaclet rewriteTaclet = tb.getRewriteTaclet();
        initConfig.getTaclet2Builder().put(rewriteTaclet, tb);
        return rewriteTaclet;
    }

}
