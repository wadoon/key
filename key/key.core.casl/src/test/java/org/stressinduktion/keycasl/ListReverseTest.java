package org.stressinduktion.keycasl;

import de.uka.ilkd.key.nparser.KeyIO;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import de.uka.ilkd.key.casl.main.Util;
import org.stressinduktion.keycasl.parser.CASLParser;
import de.uka.ilkd.key.casl.parser.CaslParser;
import de.uka.ilkd.key.casl.parser.CaslVisitor;
import de.uka.ilkd.key.casl.taclet.Taclet;
import de.uka.ilkd.key.casl.transform.Transform;

import java.io.IOException;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.EnumSet;
import java.util.List;
import java.util.logging.Logger;

import static de.uka.ilkd.key.casl.parser.CaslVisitor.*;

public class ListReverseTest {
    private static final Logger LOGGER = Util.getLogger(ListReverseTest.class);

    @Test
    public void testListReverse() throws IOException, URISyntaxException, InterruptedException {
        Alternative empty = new Alternative("nil", List.of());
        Alternative cons = new Alternative("cons",
                List.of(new OpComponent(List.of("first"), new Sort("Nat"), true),
                        new OpComponent(List.of("rest"), new Sort("NatList"), true)));

        DataType listDataType = new DataType(EnumSet.of(DataTypeFlag.FREE),
                new Sort("NatList"),
                List.of(empty, cons),
                new DataTypeDefaultValue("nil"), DataTypeExtends.EMPTY);

        OpItem append = new OpItem("append",
            new OpType(new Sort("NatList"),
                    List.of(new Sort("NatList"), new Sort("NatList")), false));

        OpItem reverse = new OpItem("reverse",
            new OpType(new Sort("NatList"),
                    List.of(new Sort("NatList")), false));

        OpItem head = new OpItem("head",
                new OpType(new Sort("Nat"),
                        List.of(new Sort("NatList")), false));

        OpItem tail = new OpItem("tail",
                new OpType(new Sort("NatList"),
                        List.of(new Sort("NatList")), false));

        OpItem size = new OpItem("size", new OpType(new Sort("int"),
                List.of(new Sort("NatList")), false));

        List<Var> vars = List.of(new Var("L", new Sort("NatList")));

        EqTerm reverseNil = new EqTerm(new FuncTerm("reverse", List.of(new IdTerm("nil"))),
                new IdTerm("nil"));

        Term reverseConsL = new FuncTerm("reverse", List.of(new IdTerm("L")));
        Term reverseConsR = new FuncTerm("append", List.of(
                new FuncTerm("reverse", List.of(new FuncTerm("tail", List.of(new IdTerm("L"))))),
                new FuncTerm("cons", List.of(new FuncTerm("head", List.of(new IdTerm("L"))), new IdTerm("nil")))
        ));

        EqTerm reverseCons = new EqTerm(reverseConsL, reverseConsR);

        Specification natList = new Specification("NatList", List.of(listDataType),
                List.of(append, reverse, head, tail, size), List.of(new FormulaEnv(reverseNil, List.of(), null), new FormulaEnv(reverseCons, vars, null)));

        Path tempDir = Files.createTempDirectory(ListReverseTest.class.getPackageName());
        try {
            Path caslFile = Path.of(this.getClass().getResource("listReverse.casl").toURI());
            LOGGER.info(Files.readString(caslFile));
            CASLParser parser = CaslParser.createParser(caslFile);
            CASLParser.Spec_defn_eofContext spec = parser.spec_defn_eof();
            CaslVisitor caslVisitor = new CaslVisitor(parser.getTokenStream());
            Specification spec_ = (Specification) caslVisitor.visit(spec);
            Assertions.assertEquals(natList, spec_);
            LOGGER.info(spec_.toString());
            Transform.Taclet transform = new Transform().transform(spec_);
            String taclet = Taclet.render(transform);
            LOGGER.info(() -> taclet);
            new KeyIO().load(taclet).parseFile();
        } finally {
            Util.rmRF(tempDir);
        }
    }
}
