package de.uka.ilkd.key.proof.io.html;

import de.uka.ilkd.key.logic.label.TermLabel;
import org.key_project.util.collection.ImmutableArray;

import java.util.Optional;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.Stack;
import java.util.function.BinaryOperator;
import java.util.stream.StreamSupport;

class HTMLCodeWriter implements AutoCloseable {
    private static final long serialVersionUID = -6017826265536761012L;
    protected StringBuilder sb = new StringBuilder();
    private int lastSeperatorInsertPosition;
    private Stack<Boolean> lastIsDiv = new Stack<>();
    private String ident = "    ";
    private int identDepth = 0;

    public HTMLCodeWriter appendf(String fmt, Object... args) {
        return append(String.format(fmt, args));
    }

    public HTMLCodeWriter appendIdent() {
        for (int i = 0; i < identDepth; i++) {
            sb.append(ident);
        }
        return this;
    }


    private HTMLCodeWriter increaseIndent() {
        identDepth++;
        return this;
    }

    private HTMLCodeWriter decreaseIndent() {
        identDepth--;
        return this;
    }

    private HTMLCodeWriter nl() {
        sb.append("\n");
        appendIdent();
        return this;
    }

    public HTMLCodeWriter append(Object obj) {
        sb.append(obj);
        return this;
    }

    public HTMLCodeWriter append(float f) {
        sb.append(f);
        return this;
    }

    public HTMLCodeWriter insert(int offset, boolean b) {
        sb.insert(offset, b);
        return this;
    }

    public int lastIndexOf(String str, int fromIndex) {
        return sb.lastIndexOf(str, fromIndex);
    }

    public char charAt(int index) {
        return sb.charAt(index);

    }

    public int codePointCount(int beginIndex, int endIndex) {
        return sb.codePointCount(beginIndex, endIndex);

    }

    public HTMLCodeWriter insert(int offset, char c) {
        sb.insert(offset, c);
        return this;
    }

    public HTMLCodeWriter append(double d) {
        sb.append(d);
        return this;
    }

    public HTMLCodeWriter insert(int dstOffset, CharSequence s) {
        sb.insert(dstOffset, s);
        return this;
    }

    public int offsetByCodePoints(int index, int codePointOffset) {
        return sb.offsetByCodePoints(index, codePointOffset);
    }

    public HTMLCodeWriter insert(int offset, long l) {
        sb.insert(offset, l);
        return this;
    }

    public HTMLCodeWriter insert(int offset, int i) {
        sb.insert(offset, i);
        return this;
    }

    public void setCharAt(int index, char ch) {
        sb.setCharAt(index, ch);

    }

    public int lastIndexOf(String str) {
        return sb.lastIndexOf(str);
    }

    public void ensureCapacity(int minimumCapacity) {
        sb.ensureCapacity(minimumCapacity);
    }

    public String substring(int start) {
        return sb.substring(start);

    }

    public HTMLCodeWriter append(char[] str) {
        sb.append(str);
        return this;
    }

    public int codePointAt(int index) {
        return sb.codePointAt(index);
    }

    public int indexOf(String str, int fromIndex) {
        return sb.indexOf(str, fromIndex);
    }

    public HTMLCodeWriter append(CharSequence s, int start, int end) {
        sb.append(s, start, end);
        return this;
    }

    public HTMLCodeWriter append(char[] str, int offset, int len) {
        sb.append(str, offset, len);
        return this;
    }

    public int codePointBefore(int index) {
        return sb.codePointBefore(index);
    }

    public HTMLCodeWriter insert(int offset, float f) {
        sb.insert(offset, f);
        return this;
    }

    public String substring(int start, int end) {
        return sb.substring(start, end);
    }

    public int length() {
        return sb.length();
    }

    public HTMLCodeWriter append(StringBuffer sb) {
        this.sb.append(sb);
        return this;
    }

    public HTMLCodeWriter reverse() {
        sb.reverse();
        return this;
    }

    public int indexOf(String str) {
        return sb.indexOf(str);
    }

    public HTMLCodeWriter insert(int offset, double d) {
        sb.insert(offset, d);
        return this;
    }

    public void trimToSize() {
        sb.trimToSize();
    }

    public void setLength(int newLength) {
        sb.setLength(newLength);
    }

    public int capacity() {
        return sb.capacity();
    }

    public HTMLCodeWriter insert(int offset, char[] str) {
        sb.insert(offset, str);
        return this;
    }

    public HTMLCodeWriter insert(int offset, String str) {
        sb.insert(offset, str);
        return this;
    }

    public HTMLCodeWriter appendCodePoint(int codePoint) {
        sb.appendCodePoint(codePoint);
        return this;
    }

    public HTMLCodeWriter append(char c) {
        sb.append(c);
        return this;
    }

    public CharSequence subSequence(int start, int end) {
        return sb.subSequence(start, end);
    }

    public HTMLCodeWriter delete(int start, int end) {
        sb.delete(start, end);
        return this;
    }

    public HTMLCodeWriter append(long lng) {
        sb.append(lng);
        return this;
    }

    public HTMLCodeWriter insert(int dstOffset, CharSequence s, int start, int end) {
        sb.insert(dstOffset, s, start, end);
        return this;
    }

    public HTMLCodeWriter insert(int index, char[] str, int offset, int len) {
        sb.insert(index, str, offset, len);
        return this;
    }

    public HTMLCodeWriter append(int i) {
        sb.append(i);
        return this;
    }

    public HTMLCodeWriter append(CharSequence s) {
        sb.append(s);
        return this;
    }

    public HTMLCodeWriter append(boolean b) {
        sb.append(b);
        return this;
    }

    public HTMLCodeWriter insert(int offset, Object obj) {
        sb.insert(offset, obj);
        return this;
    }

    public HTMLCodeWriter append(String str) {
        sb.append(str);
        return this;
    }

    public HTMLCodeWriter deleteCharAt(int index) {
        sb.deleteCharAt(index);
        return this;
    }

    public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        sb.getChars(srcBegin, srcEnd, dst, dstBegin);
    }

    public HTMLCodeWriter replace(int start, int end, String str) {
        sb.replace(start, end, str);
        return this;
    }

    @Override
    public String toString() {
        return sb.toString();
    }

    public HTMLCodeWriter deleteLast() {
        return deleteLast(1);
    }


    public HTMLCodeWriter deleteLast(int i) {
        sb.setLength(sb.length() - i);
        return this;
    }


    public HTMLCodeWriter div(String clazzes) {
        sb.append("<div class=\"" + clazzes.toLowerCase() + "\">");
        lastIsDiv.push(true);
        return this;
    }

    public HTMLCodeWriter span(String clazzes) {
        sb.append("<span class=\"" + clazzes.toLowerCase() + "\">");
        lastIsDiv.push(false);
        return this;
    }

    public HTMLCodeWriter end() {
        sb.append(lastIsDiv.pop() ? "</div>" : "</span>");
        return this;
    }

    public HTMLCodeWriter indent() {
        div("indent");
        return this;
    }

    String toClass(Section[] a) {
        return StreamSupport.stream(Spliterators.spliterator(a, Spliterator.NONNULL), false)
                .map(Object::toString)
                .reduce(implode(" ")).orElseGet(() -> "");
    }

    public HTMLCodeWriter div(Section... a) {
        return div(toClass(a));
    }

    public HTMLCodeWriter span(Section... a) {
        return span(toClass(a));
    }

    private HTMLCodeWriter keyword(String word) {
        return span(word).span(Section.KEYWORD).append(word).end().end();
    }

    HTMLCodeWriter seperator(String s) {
        lastSeperatorInsertPosition = length();
        span(Section.SEPARATOR).append(s);
        return this.end();
    }


    private HTMLCodeWriter variable(String variable) {
        if (variable.contains("$")) {
            span(Section.SPECIAL_VARIABLE).span(Section.VARIABLE).append(variable);
            return this.end().end();
        }
        span(Section.VARIABLE).append(variable);
        return this.end();
    }


    private HTMLCodeWriter ts() {
        return seperator(";");
    }

    private HTMLCodeWriter type(String baseTypeName) {
        span(Section.TYPE_NAME).append(baseTypeName);
        return this.end();
    }

    private HTMLCodeWriter operator(String s) {
        span(Section.OPERATOR).append(s);
        return this.end();
    }

    private HTMLCodeWriter deleteLastSeparator() {
        sb.setLength(lastSeperatorInsertPosition);
        return this;

    }

    public HTMLCodeWriter span(ImmutableArray<TermLabel> labels) {
        Spliterator<TermLabel> iter = Spliterators.spliteratorUnknownSize(labels.iterator(), Spliterator.IMMUTABLE);
        Optional<String> clazzes = StreamSupport.stream(iter, false)
                .map((TermLabel lbl) -> lbl.name().toString())
                .reduce(implode(" "));

        if (clazzes.isPresent())
            return span(clazzes.get());
        else
            return span();
    }

    public static BinaryOperator<String> implode(String delimter) {
        return (String a, String b) -> {
            return a + " " + b;
        };
    }

    @Override
    public void close() throws Exception {
        end();
    }
}