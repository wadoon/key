package org.key_project.key.tptp;

import de.uka.ilkd.key.tptp.tptp_v7_0_0_0Lexer;
import de.uka.ilkd.key.tptp.tptp_v7_0_0_0Parser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Path;

public class Facade {
    private Facade() {
    }

    public static void include(Path path) throws IOException {
        include(path, new Tptp2KeyTranslator(path));
    }
    public static void include(Path path, Tptp2KeyTranslator parent) throws IOException {
        var parsed = parseTptpFile(path);
        parsed.accept(new Tptp2KeyTranslator(path, parent.output));
    }

    public static void translateTptpFile(Path tptpFile, PrintWriter target) throws IOException {
        var tptpParsed = parseTptpFile(tptpFile);
        var v = new Tptp2KeyTranslator(tptpFile);
        tptpParsed.accept(v);
        v.output.writeTo(target);
        target.flush();
        target.close();
    }

    private static  ParserRuleContext parseTptpFile(Path tptpFile) throws IOException {
        var input = CharStreams.fromPath(tptpFile);
        var lexer = new tptp_v7_0_0_0Lexer(input);
        var stream = new CommonTokenStream(lexer);
        var parser = new tptp_v7_0_0_0Parser(stream);
        return parser.tptp_file();
    }
}
