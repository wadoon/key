package edu.kit.iti.formal.psdbg.lint;


import com.github.mustachejava.DefaultMustacheFactory;
import com.github.mustachejava.Mustache;
import com.github.mustachejava.reflect.ReflectionObjectHandler;
import edu.kit.iti.formal.psdbg.parser.ast.ASTNode;
import lombok.Data;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.io.StringReader;
import java.io.StringWriter;
import java.lang.reflect.Array;
import java.util.*;

/**
 * @author Alexander Weigl
 * @version 1 (23.05.17)
 */
@Data
@RequiredArgsConstructor
public class LintProblem {
    @Getter
    private final Issue issue;
    private final Mustache template;

    @Getter
    private List<Token> markTokens = new ArrayList<>();

    private static DefaultMustacheFactory mf = new DefaultMustacheFactory();

    static {
        ReflectionObjectHandler oh = new ReflectionObjectHandler() {
            @Override
            public Object coerce(final Object object) {
                if (object != null && object.getClass().isArray()) {
                    return new ArrayMap(object);
                }

                if (object != null && List.class.isAssignableFrom(object.getClass())) {
                    return new ListMap((List) object);
                }
                return super.coerce(object);
            }
        };
        mf.setObjectHandler(oh);
    }

    public LintProblem(Issue issue) {
        this.issue = issue;
        template = mf.compile(new StringReader(
                issue.getMessage()), issue.name());
    }

    public Token[] toks() {
        Token[] tokens = (Token[]) markTokens.toArray(new Token[markTokens.size()]);
        return tokens;
    }

    public Token getFirstToken() {
        if (markTokens.size() == 0)
            return null;
        return markTokens.get(0);
    }

    public int getLineNumber() {
        if (getFirstToken() == null)
            return -1;
        return getFirstToken().getLine();
    }

    public static LintProblem create(Issue issue, Token... markTokens) {
        LintProblem lp = new LintProblem(issue);
        return lp.tokens(markTokens);
    }


    public String getMessage() {
        StringWriter sw = new StringWriter();
        template.execute(sw, this);
        return sw.toString();
    }

    public static <T extends ParserRuleContext>
    LintProblem create(Issue issue, ASTNode<T>... nodes) {
        return new LintProblem(issue).nodes(nodes);
    }

    public <T extends ParserRuleContext> LintProblem nodes(ASTNode<T>... nodes) {
        for (ASTNode n : nodes) {
            ParserRuleContext ctx = n.getRuleContext();
            if (ctx != null)
                markTokens.add(ctx.getStart());
        }
        return this;
    }

    public LintProblem tokens(Token... toks) {
        getMarkTokens().addAll(Arrays.asList(toks));
        return this;
    }

    public boolean includeTextPosition(int chIdx) {
        //weigl: a little more relaxer that have to. Think on one length tokens.
        return markTokens.stream().anyMatch(
                tok -> tok.getStartIndex() - 2 <= chIdx && chIdx - 2 <= tok.getStopIndex());
    }
}

class ListMap<V> extends AbstractMap<Integer, V>
        implements Iterable<V> {
    private final List<V> list;

    public ListMap(List<V> list) {
        this.list = list;
    }

    @Override
    public V get(Object key) {
        try {
            Integer i = (Integer) key;
            return list.get(i);
        } catch (ClassCastException e) {
            return null;
        }
    }

    @Override
    public Set<Entry<Integer, V>> entrySet() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Iterator<V> iterator() {
        return list.iterator();
    }
}

class ArrayMap extends AbstractMap<Object, Object> implements Iterable<Object> {
    private final Object object;

    public ArrayMap(Object object) {
        this.object = object;
    }

    @Override
    public Object get(Object key) {
        try {
            int index = Integer.parseInt(key.toString());
            return Array.get(object, index);
        } catch (NumberFormatException nfe) {
            return null;
        }
    }

    @Override
    public boolean containsKey(Object key) {
        return get(key) != null;
    }

    @Override
    public Set<Entry<Object, Object>> entrySet() {
        throw new UnsupportedOperationException();
    }

    /**
     * Returns an iterator over a set of elements of type T.
     *
     * @return an Iterator.
     */
    @Override
    public Iterator<Object> iterator() {
        return new Iterator<Object>() {

            int index = 0;
            int length = Array.getLength(object);

            @Override
            public boolean hasNext() {
                return index < length;
            }

            @Override
            public Object next() {
                return Array.get(object, index++);
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }
}
