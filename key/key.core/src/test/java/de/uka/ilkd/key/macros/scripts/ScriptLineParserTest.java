package de.uka.ilkd.key.macros.scripts;

import org.junit.Test;

import java.io.StringReader;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (7/25/21)
 */
public class ScriptLineParserTest {
    @Test
    public void test() throws Exception {
        String arg = "macro key1=value1 key2=\"value two\" defval3 \"long defvalue\"; " +
                "command ; \n\n" +
                "# some comment\n" +
                "multiline #comment internal\n command \n with=\"line breaks in \n values\"; \n" +
                "select formula=\"a;b\"; \n" +
                "hyphened-command;\n";

        ScriptLineParser mlp = new ScriptLineParser(new StringReader(arg));
        Map<String, String> str;
        while((str = mlp.parseCommand()) != null) {
            System.err.println(str);
        }
    }
}