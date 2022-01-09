package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.collection.ImmutableList;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.*;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

/**
 * @author Alexander Weigl
 * @version 1 (5/14/20)
 */
@RunWith(Parameterized.class)
public class NJmlOverloadedOperatorTests {
    @Parameterized.Parameter
    public String expr;

    @Parameterized.Parameter(1)
    public String expected;

    private JmlIO jmlIO;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        try (InputStream s = NJmlOverloadedOperatorTests.class.getResourceAsStream("overloaded_operators.txt");
             BufferedReader reader = new BufferedReader(new InputStreamReader(Objects.requireNonNull(s)))) {
            String l;
            while ((l = reader.readLine()) != null) {
                if (l.trim().isEmpty() || l.startsWith("#")) {
                    continue;
                }
                String[] a = l.split("=====>");
                seq.add(new Object[]{a[0], a[1].trim()});
            }
        }
        return seq;
    }

    private Services services;

    @Before
    public void setup() {
        if (services != null) return;
        services = TacletForTests.services();
        var r2k = new Recoder2KeY(services, services.getNamespaces());
        r2k.parseSpecialClasses();
        var kjt = new KeYJavaType(Sort.ANY);
        var self = new LocationVariable(new ProgramElementName("self"), kjt);
        var result = new LocationVariable(new ProgramElementName("result"), kjt);
        var exc = new LocationVariable(new ProgramElementName("exc"), kjt);

        var sortLocset = services.getTypeConverter().getLocSetLDT().targetSort();
        var sortSeq = services.getTypeConverter().getSeqLDT().targetSort();
        var l1 = new LocationVariable(new ProgramElementName("l1"), sortLocset);
        var l2 = new LocationVariable(new ProgramElementName("l2"), sortLocset);
        var s1 = new LocationVariable(new ProgramElementName("s1"), sortSeq);
        var s2 = new LocationVariable(new ProgramElementName("s2"), sortSeq);
        jmlIO = new JmlIO(services, kjt, self, ImmutableList.fromList(Arrays.asList(l1, l2, s1, s2)),
                result, exc, new HashMap<>(), new HashMap<>());
    }

    @Test
    public void parseAndInterpret() {
        Term actual = jmlIO.parseExpression(expr);
        assertNotNull(actual);
        assertEquals(expected, actual.toString());
    }
}