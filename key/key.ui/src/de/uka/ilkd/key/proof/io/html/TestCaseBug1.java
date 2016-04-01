package de.uka.ilkd.key.proof.io.html;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;

import java.util.HashMap;

/**
 * Created by weigl on 4/1/16.
 */
public class TestCaseBug1 {
    public static void main(String argv[]) {
        TermFactory termFactory = new TermFactory(new HashMap<>());
        Term p = termFactory.createTerm(new Function(new Name("p"), Sort.FORMULA));
        Term flse = termFactory.createTerm(Junctor.FALSE);

        SequentFormula b = new SequentFormula(p);
        SequentFormula c = new SequentFormula(flse);

        Semisequent a = new Semisequent(b);
        Semisequent d = a.insertFirst(c).semisequent();

        System.out.println(d);
        System.out.println(LogicPrinter.quickPrintSemisequent(d, null));
    }
}
