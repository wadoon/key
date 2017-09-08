package de.uka.ilkd.key.macros.scripts.meta;

import de.uka.ilkd.key.macros.scripts.EngineState;
import de.uka.ilkd.key.macros.scripts.RuleCommand;
import org.junit.Test;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (08.09.17)
 */
public class ArgumentsLifterTest {
    @Test
    public void inferScriptArguments() throws Exception {
        List<ProofScriptArgument> args = ArgumentsLifter.inferScriptArguments(RuleCommand.Parameters.class);
        assertEquals(5, args.size());
    }

    @Test
    public void instantiationOfRuleCommand() throws Exception {
        ValueInjector vi = ValueInjector.createDefault();

        Map<String, String> args = new HashMap<>();
        args.put("formula", "p(x)");
        args.put("occ", "1");
        args.put("#2", "blubber");

        args.put("inst_ABC", "afklsyc");
        args.put("inst_qbe", "klfjdsalnxcmvnf");
        args.put("inst_252", "flfs");


        TestParameters p = new TestParameters();
        vi.inject(p, args);

        assertEquals("p(x)", p.formula.toString());
        assertEquals(1, p.occ);
        assertEquals("blubber", p.rulename);

        assertEquals("afklsyc", p.instantiations.get("ABC"));
        assertEquals("klfjdsalnxcmvnf", p.instantiations.get("qbe"));
        assertEquals("flfs", p.instantiations.get("252"));
        assertEquals(3, p.instantiations.size());

    }


    public <K, V> Map<K, V> asMap(Collection<V> seq, Function<V, K> func) {
        HashMap<K, V> map = new HashMap<>();
        for (V v : seq) {
            map.put(func.apply(v), v);
        }
        return map;
    }

    public static class TestParameters {
        @Option(value="#2") public  String rulename;
        @Option(value="on", required = false) public String on;
        @Option(value="formula", required = false) public String formula;
        @Option(value="occ", required = false) public  int occ = -1;
        @Varargs(as=String.class, prefix="inst_")
        public Map<String, String> instantiations = new HashMap<>();
    }

}