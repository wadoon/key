package de.uka.ilkd.key.casl;

import de.uka.ilkd.key.casl.parser.CaslParser;
import de.uka.ilkd.key.casl.parser.CaslVisitor;
import de.uka.ilkd.key.casl.taclet.Taclet;
import de.uka.ilkd.key.casl.transform.Transform;
import de.uka.ilkd.key.casl.parser.CASLParser;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.io.IOException;
import java.nio.file.Path;

public class CaslFacade {
    private static final Logger LOGGER = LoggerFactory.getLogger(CaslFacade.class);

    public static void main(String[] args) throws IOException {
        System.out.println("TODO: help text");
    }

    public static String process(Path source, @Nullable String problem) throws IOException, InterruptedException {
        CASLParser parser = CaslParser.createParser(source);
        var ctx = parser.spec_defn_eof();
        CaslVisitor visitor = new CaslVisitor(parser.getTokenStream());
        CaslVisitor.Specification spec = (CaslVisitor.Specification) visitor.visit(ctx);
        Transform tr = new Transform();
        if (problem != null) {
            tr.problem(problem);
        }
        Transform.Taclet transform = tr.transform(spec);
        return Taclet.render(transform);
    }
}
