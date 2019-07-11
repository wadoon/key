package de.uka.ilkd.key.macros.scripts;

import org.jetbrains.annotations.NotNull;
import org.junit.Assert;
import org.junit.Test;

import java.io.IOException;
import java.io.StringReader;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (11.07.19)
 */
public class ScriptLineParserTest {
    @Test
    public void fullSingleCommand() throws IOException, ScriptException {
        String script = "abc-def key1=value1 key2=\"value two\" defval3 \"long defvalue\";";
        Map<String, String> result = parse(script);
        Assert.assertNotNull(result);
        Assert.assertEquals("{#1=abc-def, #2=defval3, #3=long defvalue, key1=value1, key2=value two}",
                result.toString());
    }

    @Test
    public void fullCommandLexer() throws IOException, ScriptException {
        String script = "@ma-cro key1=value1 key2=\"value two\" defval3 \"long defvalue\";";
        ScriptLineLexer lexer = new ScriptLineLexer();
        for (int i = 0; i < script.length(); i++) {
            lexer.feed(script.charAt(i));
        }
        @NotNull List<Token> toks = lexer.fetchAllAndClear();
        List<String> values = toks.stream().map(it -> it.text).collect(Collectors.toList());
        Assert.assertEquals(Arrays.asList("@ma-cro", "key1", "=", "value1", "key2", "=", "value two", "defval3", "long defvalue", ";"),
                values);

        Assert.assertEquals(1, lexer.line);
        Assert.assertEquals(61, lexer.col);
        Assert.assertEquals(lexer.getPosition(), lexer.col);
        Assert.assertTrue(lexer.fetchAllAndClear().isEmpty());
        Assert.assertNull(lexer.getLastToken());
    }

    private Map<String, String> parse(String script) throws IOException, ScriptException {
        ScriptLineParser parser = new ScriptLineParser(new StringReader(script));
        return new TreeMap<>(parser.getNextCommand()); //TreeMap for sorted keys
    }


    @Test
    public void batchCommands() throws IOException, ScriptException {
        String script = "macro key1=value1 key2=\"value two\" defval3 \"long defvalue\"; " +
                "command ; \n\n\t\t\thyphened-command;" +
                "# some comment\n" +
                "multiline #comment internal\n command \n with=\"line breaks in \n values\"; \n" +
                "select formula=\"a;b\"; \n" +
                "hyphened-command;\n";

        System.out.println(script);
        StringBuilder sb = new StringBuilder();
        ScriptLineParser parser = new ScriptLineParser(new StringReader(script));
        for (int i = 0; i < 6; i++) {
            Map<String, String> c = parser.getNextCommand();
            sb.append(c != null ? new TreeMap<>(c).toString() : "null").append('\n');
        }
        System.out.println(sb.toString());

        Assert.assertEquals("{#1=macro, #2=defval3, #3=long defvalue, key1=value1, key2=value two}\n" +
                "{#1=command}\n" +
                "{#1=hyphened-command}\n" +
                "{#1=multiline, #2=command, with=line breaks in \n" +
                " values}\n" +
                "{#1=select, formula=a;b}\n" +
                "{#1=hyphened-command}\n", sb.toString());

    }

}