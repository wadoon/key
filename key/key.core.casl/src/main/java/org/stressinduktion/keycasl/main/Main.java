package org.stressinduktion.keycasl.main;

import de.uka.ilkd.key.nparser.KeyIO;
import org.stressinduktion.keycasl.parser.CASLParser;
import org.stressinduktion.keycasl.parser.CaslParser;
import org.stressinduktion.keycasl.parser.CaslVisitor;
import org.stressinduktion.keycasl.taclet.Taclet;
import org.stressinduktion.keycasl.transform.Transform;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Main {
    static private final Logger LOGGER = Util.getLogger(Main.class);
    static {
        Util.enableLogging(Level.ALL);
    }

    public static void main(String[] args) throws IOException {
        System.out.println("TODO: help text");
    }

    public static String process(Path source, String problem) throws IOException, InterruptedException {
        System.out.println(Files.readString(source));
        CASLParser parser = CaslParser.createParser(source);
        CASLParser.Spec_defn_eofContext spec_defn_eofContext = parser.spec_defn_eof();
        CaslVisitor visitor = new CaslVisitor(parser.getTokenStream());
        CaslVisitor.Specification spec = (CaslVisitor.Specification) visitor.visit(spec_defn_eofContext);
        Transform tr = new Transform();
        if (problem != null) {
            tr.problem(problem);
        }
        Transform.Taclet transform = tr.transform(spec);
        return Taclet.render(transform);
    }
}
