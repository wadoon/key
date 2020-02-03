package de.uka.ilkd.key.strategy.normalization;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

public class SimpleFormulaNormalizationTest {


    private Proof proof;
    private Goal g;

    private Namespace<QuantifiableVariable> variables = new Namespace<>();
    private Namespace<Function> functions = new Namespace<>();
    private Namespace<Sort> sorts = new Namespace<>();

    private Sort s;
    private Function s_a;
    private Function s_b;
    private Function s_c;

    private Function f_f;
    private Function f_g;

    public SimpleFormulaNormalizationTest() { super(); }

    @Before
    public void setUp() {
        // Sorts
        s = new SortImpl(new Name("S"));
        sorts.add(s);
        // Constants
        s_a = new Function(new Name("a"), s, new Sort[0]);
        s_b = new Function(new Name("a"), s, new Sort[0]);
        s_c = new Function(new Name("a"), s, new Sort[0]);
        functions.add(s_a);
        functions.add(s_b);
        functions.add(s_c);
        // Functions
        f_f = new Function(new Name("f"), s, new Sort[] {s});
        f_g = new Function(new Name("g"), s, new Sort[] {s});
        functions.add(f_f);
        functions.add(f_g);

    }

    @Test
    public void TestNormalization() {
        assertTrue(true);
    }

}