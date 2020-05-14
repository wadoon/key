package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.JavaProfile;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.key_project.util.collection.ImmutableSLList;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (5/14/20)
 */
@RunWith(Parameterized.class)
public class ExpressionTranslatorTest {
    @Parameterized.Parameter
    public String expr;

    @Parameterized.Parameters(name = "{0}")
    public static Collection<Object[]> getFiles() throws IOException {
        List<Object[]> seq = new LinkedList<>();
        try (InputStream s = ExpressionTranslatorTest.class.getResourceAsStream("exprs.txt");
             BufferedReader reader = new BufferedReader(new InputStreamReader(s))) {
            String l;
            while ((l = reader.readLine()) != null) {
                if (l.trim().isEmpty() || l.startsWith("#")) {
                    continue;
                }
                seq.add(new Object[]{l});
            }
        }
        return seq;
    }

    @Test
    public void parseAndInterpret() {
        Services services = new Services(JavaProfile.getDefaultProfile());
        ProgramVariable self = new LocationVariable(new ProgramElementName("self"), Sort.ANY);
        ProgramVariable result = new LocationVariable(new ProgramElementName("result"), Sort.ANY);
        ProgramVariable exc = new LocationVariable(new ProgramElementName("exc"), Sort.ANY);
        Term t = new InterpretJml(
                services, null, self, ImmutableSLList.nil(), result, exc,
                new HashMap<>(), new HashMap<>())
                .parseExpr(expr);
        System.out.println(t);
    }

}