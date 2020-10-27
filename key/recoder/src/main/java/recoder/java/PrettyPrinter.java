package recoder.java;

import recoder.io.PropertyNames;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.*;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTList;
import recoder.util.StringUtils;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

public class PrettyPrinter extends SourceVisitor implements PropertyNames {
    private static final char[] BLANKS = new char[128];
    private static final char[] FEEDS = new char[8];

    static {
        int i;
        for (i = 0; i < FEEDS.length; i++)
            FEEDS[i] = '\n';
        for (i = 0; i < BLANKS.length; i++)
            BLANKS[i] = ' ';
    }

    private final Properties properties;
    private Writer out = null;
    private int line = 1;
    private int column = 1;
    private int level = 0;
    private final List<SingleLineComment> singleLineCommentWorkList = new ArrayList<SingleLineComment>();
    private boolean isPrintingSingleLineComments = false;
    private boolean hasJustPrintedComment = false;
    private final SourceElement.Position overwritePosition;
    private int indentation;
    private boolean overwriteIndentation;
    private boolean overwriteParsePositions;

    protected PrettyPrinter(Writer out, Properties props) {
        this.overwritePosition = new SourceElement.Position(0, 0);
        setWriter(out);
        this.properties = props;
        cacheFrequentlyUsed();
    }

    protected static String encodeUnicodeChars(String str) {
        int len = str.length();
        StringBuffer buf = new StringBuffer(len + 4);
        for (int i = 0; i < len; i++) {
            char c = str.charAt(i);
            if (c >= '\u0100') {
                if (c < '\u1000') {
                    buf.append("\\u0" + Integer.toString(c, 16));
                } else {
                    buf.append("\\u" + Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    public Writer getWriter() {
        return this.out;
    }

    public void setWriter(Writer out) {
        if (out == null)
            throw new IllegalArgumentException("Impossible to write to null");
        this.out = out;
        this.column = 1;
        this.line = 1;
        this.singleLineCommentWorkList.clear();
        this.isPrintingSingleLineComments = false;
    }

    public int getLine() {
        return this.line;
    }

    public int getColumn() {
        return this.column;
    }

    public int getIndentationLevel() {
        return this.level;
    }

    public void setIndentationLevel(int level) {
        this.level = level;
    }

    public int getTotalIndentation() {
        return this.indentation * this.level;
    }

    public void changeLevel(int delta) {
        this.level += delta;
    }

    protected void printIndentation(int lf, int blanks) {
        if (lf > 0)
            do {
                int n = Math.min(lf, FEEDS.length);
                print(FEEDS, 0, n);
                lf -= n;
            } while (lf > 0);
        while (blanks > 0) {
            int n = Math.min(blanks, BLANKS.length);
            print(BLANKS, 0, n);
            blanks -= n;
        }
    }

    protected SourceElement.Position setElementIndentation(int minlf, int minblanks, SourceElement element) {
        SourceElement.Position indent = element.getRelativePosition();
        if (this.hasJustPrintedComment && element.getStartPosition() == SourceElement.Position.UNDEFINED && element.getStartPosition() == SourceElement.Position.UNDEFINED)
            minlf = Math.max(1, minlf);
        this.hasJustPrintedComment = false;
        if (indent == SourceElement.Position.UNDEFINED) {
            if (minlf > 0)
                minblanks += getTotalIndentation();
            indent = new SourceElement.Position(minlf, minblanks);
        } else if (this.overwriteIndentation) {
            if (minlf > 0)
                minblanks += getTotalIndentation();
            indent.setPosition(minlf, minblanks);
        } else {
            if (minlf > 0 && indent.getColumn() == 0 && indent.getLine() == 0)
                indent.setLine(1);
            if (indent.getLine() > 0 && !(element instanceof Comment))
                minblanks += getTotalIndentation();
            if (minblanks > indent.getColumn())
                indent.setColumn(minblanks);
        }
        element.setRelativePosition(indent);
        return indent;
    }

    protected void printElementIndentation(int minlf, int minblanks, SourceElement element) {
        SourceElement.Position indent = setElementIndentation(minlf, minblanks, element);
        printIndentation(indent.getLine(), indent.getColumn());
        if (this.overwriteParsePositions) {
            indent.setPosition(this.line, this.column);
            element.setStartPosition(indent);
        }
    }

    protected void printElementIndentation(int minblanks, SourceElement element) {
        printElementIndentation(0, minblanks, element);
    }

    protected void printElementIndentation(SourceElement element) {
        printElementIndentation(0, 0, element);
    }

    protected void printElement(int lf, int levelChange, int blanks, SourceElement elem) {
        this.level += levelChange;
        setElementIndentation(lf, blanks, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    protected void printElement(int lf, int blanks, SourceElement elem) {
        setElementIndentation(lf, blanks, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    protected void printElement(int blanks, SourceElement elem) {
        setElementIndentation(0, blanks, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    protected void printElement(SourceElement elem) {
        setElementIndentation(0, 0, findFirstElementInclComment(elem));
        elem.accept(this);
    }

    protected void printProgramElementList(int firstLF, int levelChange, int firstBlanks, String separationSymbol, int separationLF, int separationBlanks, List<? extends ProgramElement> list) {
        int s = list.size();
        if (s == 0)
            return;
        printElement(firstLF, levelChange, firstBlanks, list.get(0));
        for (int i = 1; i < s; i++) {
            print(separationSymbol);
            printElement(separationLF, separationBlanks, list.get(i));
        }
    }

    protected void printKeywordList(List<? extends ProgramElement> list) {
        printProgramElementList(0, 0, 0, "", 0, 1, list);
    }

    protected void printCommaList(int firstLF, int levelChange, int firstBlanks, List<? extends ProgramElement> list) {
        printProgramElementList(firstLF, levelChange, firstBlanks, ",", 0, 1, list);
    }

    protected void printCommaList(int separationBlanks, List<? extends ProgramElement> list) {
        printProgramElementList(0, 0, 0, ",", 0, separationBlanks, list);
    }

    protected void printCommaList(List<? extends ProgramElement> list) {
        printProgramElementList(0, 0, 0, ",", 0, 1, list);
    }

    protected void printLineList(int firstLF, int levelChange, List<? extends ProgramElement> list) {
        printProgramElementList(firstLF, levelChange, 0, "", 1, 0, list);
    }

    protected void printBlockList(int firstLF, int levelChange, List<? extends ProgramElement> list) {
        printProgramElementList(firstLF, levelChange, 0, "", 2, 0, list);
    }

    private void dumpComments() {
        int size = this.singleLineCommentWorkList.size();
        if (size > 0) {
            this.isPrintingSingleLineComments = true;
            for (int i = 0; i < size; i++)
                this.singleLineCommentWorkList.get(i).accept(this);
            this.singleLineCommentWorkList.clear();
            this.isPrintingSingleLineComments = false;
        }
    }

    protected void print(int c) {
        if (c == 10) {
            if (!this.isPrintingSingleLineComments)
                dumpComments();
            this.column = 1;
            this.line++;
        } else {
            this.column++;
        }
        try {
            this.out.write(c);
        } catch (IOException ioe) {
            throw new PrettyPrintingException(ioe);
        }
    }

    protected void print(char[] cbuf, int off, int len) {
        boolean col = false;
        for (int i = off + len - 1; i >= off; i--) {
            if (cbuf[i] == '\n') {
                if (!this.isPrintingSingleLineComments)
                    dumpComments();
                this.line++;
                if (!col) {
                    this.column = off + len - 1 - i + 1;
                    col = true;
                }
            }
        }
        if (!col)
            this.column += len;
        try {
            this.out.write(cbuf, off, len);
        } catch (IOException ioe) {
            throw new PrettyPrintingException(ioe);
        }
    }

    protected void print(String str) {
        int i = str.lastIndexOf('\n');
        if (i >= 0) {
            this.column = str.length() - i + 1 + 1;
            do {
                dumpComments();
                this.line++;
                i = str.lastIndexOf('\n', i - 1);
            } while (i >= 0);
        } else {
            this.column += str.length();
        }
        try {
            this.out.write(str);
        } catch (IOException ioe) {
            throw new PrettyPrintingException(ioe);
        }
    }

    public boolean getBooleanProperty(String key) {
        return StringUtils.parseBooleanProperty(this.properties.getProperty(key));
    }

    private void cacheFrequentlyUsed() {
        this.indentation = Integer.parseInt(this.properties.getProperty("indentationAmount"));
        if (this.indentation < 0)
            throw new IllegalArgumentException("Negative indentation");
        this.overwriteIndentation = getBooleanProperty("overwriteIndentation");
        this.overwriteParsePositions = getBooleanProperty("overwriteParsePositions");
    }

    protected int getIndentation() {
        return this.indentation;
    }

    protected boolean isOverwritingIndentation() {
        return this.overwriteIndentation;
    }

    protected boolean isOverwritingParsePositions() {
        return this.overwriteParsePositions;
    }

    protected void printHeader(int lf, int blanks, ProgramElement elem) {
        printHeader(lf, 0, blanks, elem);
    }

    protected void printHeader(int blanks, ProgramElement elem) {
        printHeader(0, 0, blanks, elem);
    }

    protected void printHeader(ProgramElement elem) {
        printHeader(0, 0, 0, elem);
    }

    private SourceElement findFirstElementInclComment(SourceElement x) {
        if (!(x instanceof ProgramElement))
            return x.getFirstElement();
        ASTList<Comment> aSTList = ((ProgramElement) x).getComments();
        int s = (aSTList == null) ? 0 : aSTList.size();
        for (int i = 0; i < s; i++) {
            Comment c = aSTList.get(i);
            if (c.isPrefixed())
                return c;
        }
        return x.getFirstElement();
    }

    protected void printHeader(int lf, int levelChange, int blanks, ProgramElement x) {
        this.level += levelChange;
        if (lf > 0)
            blanks += getTotalIndentation();
        SourceElement first = findFirstElementInclComment(x);
        setElementIndentation(lf, blanks, first);
        this.hasJustPrintedComment = false;
        int s = (x.getComments() != null) ? x.getComments().size() : 0;
        for (int i = 0; i < s; i++) {
            Comment c = x.getComments().get(i);
            if (c.isPrefixed()) {
                c.accept(this);
                this.hasJustPrintedComment = true;
            }
        }
    }

    protected void printFooter(ProgramElement x) {
        if (this.overwriteParsePositions) {
            this.overwritePosition.setPosition(this.line, this.column);
            x.setEndPosition(this.overwritePosition);
        }
        int s = (x.getComments() != null) ? x.getComments().size() : 0;
        for (int i = 0; i < s; i++) {
            Comment c = x.getComments().get(i);
            if (!c.isPrefixed() && !c.isContainerComment())
                if (c instanceof SingleLineComment) {
                    this.singleLineCommentWorkList.add((SingleLineComment) c);
                } else {
                    c.accept(this);
                }
        }
    }

    protected boolean printContainerComments(ProgramElement x) {
        boolean commentPrinted = false;
        int s = (x.getComments() != null) ? x.getComments().size() : 0;
        for (int i = 0; i < s; i++) {
            Comment c = x.getComments().get(i);
            if (c.isContainerComment()) {
                c.accept(this);
                printIndentation(1, getIndentation());
                commentPrinted = true;
            }
        }
        return commentPrinted;
    }

    protected void printOperator(Operator x, String symbol) {
        ASTList<SourceElement> aSTList = x.getArguments();
        if (aSTList != null) {
            boolean addParentheses = x.isToBeParenthesized();
            if (addParentheses)
                print(40);
            switch (x.getArity()) {
                case 2:
                    printElement(0, aSTList.get(0));
                    if (getBooleanProperty("glueInfixOperators")) {
                        printElementIndentation(0, x);
                        print(symbol);
                        printElement(aSTList.get(1));
                        break;
                    }
                    printElementIndentation(1, x);
                    print(symbol);
                    printElement(1, aSTList.get(1));
                    break;
                case 1:
                    switch (x.getNotation()) {
                        case 0:
                            printElementIndentation(x);
                            print(symbol);
                            if (getBooleanProperty("glueUnaryOperators")) {
                                printElement(0, aSTList.get(0));
                                break;
                            }
                            printElement(1, aSTList.get(0));
                            break;
                        case 2:
                            printElement(0, aSTList.get(0));
                            if (getBooleanProperty("glueUnaryOperators")) {
                                printElementIndentation(x);
                                print(symbol);
                                break;
                            }
                            printElementIndentation(1, x);
                            print(symbol);
                            break;
                    }
                    break;
            }
            if (addParentheses)
                print(41);
            if (x instanceof Assignment && (
                    (Assignment) x).getStatementContainer() != null)
                print(59);
        }
    }

    public void visitIdentifier(Identifier x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getText());
        printFooter(x);
    }

    public void visitIntLiteral(IntLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitBooleanLiteral(BooleanLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue() ? "true" : "false");
        printFooter(x);
    }

    public void visitStringLiteral(StringLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void visitNullLiteral(NullLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print("null");
        printFooter(x);
    }

    public void visitCharLiteral(CharLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(encodeUnicodeChars(x.getValue()));
        printFooter(x);
    }

    public void visitDoubleLiteral(DoubleLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitLongLiteral(LongLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitFloatLiteral(FloatLiteral x) {
        printHeader(x);
        printElementIndentation(x);
        print(x.getValue());
        printFooter(x);
    }

    public void visitPackageSpecification(PackageSpecification x) {
        printHeader(x);
        int m = 0;
        if (x.getAnnotations() != null && x.getAnnotations().size() > 0) {
            m = x.getAnnotations().size();
            printKeywordList(x.getAnnotations());
            m = 1;
        }
        printElementIndentation(m, x);
        print("package");
        printElement(1, x.getPackageReference());
        print(59);
        printFooter(x);
    }

    public void visitTypeReference(TypeReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(46);
        }
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        if (x.getTypeArguments() != null && x.getTypeArguments().size() > 0) {
            print(60);
            printCommaList(x.getTypeArguments());
            print(62);
        }
        for (int i = 0; i < x.getDimensions(); i++)
            print("[]");
        printFooter(x);
    }

    public void visitPackageReference(PackageReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(46);
        }
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        printFooter(x);
    }

    public void visitThrows(Throws x) {
        printHeader(x);
        if (x.getExceptions() != null) {
            printElementIndentation(x);
            print("throws");
            printCommaList(0, 0, 1, x.getExceptions());
        }
        printFooter(x);
    }

    public void visitArrayInitializer(ArrayInitializer x) {
        printHeader(x);
        printElementIndentation(x);
        print(123);
        printContainerComments(x);
        if (x.getArguments() != null)
            printCommaList(0, 0, 1, x.getArguments());
        if (x.getArguments() != null && x.getArguments().size() > 0 && x.getRelativePosition().getLine() > 0) {
            printIndentation(1, getTotalIndentation());
            print(125);
        } else {
            print(" }");
        }
        printFooter(x);
    }

    public void visitElementValueArrayInitializer(ElementValueArrayInitializer x) {
        printHeader(x);
        printElementIndentation(x);
        print(123);
        if (x.getElementValues() != null)
            printCommaList(0, 0, 1, x.getElementValues());
        if (x.getElementValues() != null && x.getElementValues().size() > 0 && x.getRelativePosition().getLine() > 0) {
            printIndentation(1, getTotalIndentation());
            print(125);
        } else {
            print(" }");
        }
        printFooter(x);
    }

    public void visitCompilationUnit(CompilationUnit x) {
        this.line = this.column = 1;
        printHeader(x);
        setIndentationLevel(0);
        boolean hasPackageSpec = (x.getPackageSpecification() != null);
        if (hasPackageSpec)
            printElement(x.getPackageSpecification());
        boolean hasImports = (x.getImports() != null && x.getImports().size() > 0);
        if (hasImports)
            printLineList((x.getPackageSpecification() != null) ? 2 : 1, 0, x.getImports());
        if (x.getDeclarations() != null)
            printBlockList((hasImports || hasPackageSpec) ? 2 : 0, 0, x.getDeclarations());
        printFooter(x);
        printIndentation(1, 0);
    }

    public void visitClassDeclaration(ClassDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null)
            m = x.getDeclarationSpecifiers().size();
        if (m > 0) {
            printKeywordList(x.getDeclarationSpecifiers());
            m = 1;
        }
        if (x.getIdentifier() != null) {
            printElementIndentation(m, x);
            print("class");
            printElement(1, x.getIdentifier());
        }
        if (x.getTypeParameters() != null && x.getTypeParameters().size() > 0) {
            print("<");
            printCommaList(x.getTypeParameters());
            print("> ");
        }
        if (x.getExtendedTypes() != null)
            printElement(1, x.getExtendedTypes());
        if (x.getImplementedTypes() != null)
            printElement(1, x.getImplementedTypes());
        if (x.getIdentifier() != null)
            print(32);
        print(123);
        printContainerComments(x);
        if (x.getMembers() != null && !x.getMembers().isEmpty()) {
            printBlockList(2, 1, x.getMembers());
            changeLevel(-1);
        }
        printIndentation(1, getTotalIndentation());
        print(125);
        printFooter(x);
    }

    public void visitInterfaceDeclaration(InterfaceDeclaration x) {
        visitInterfaceDeclaration(x, false);
    }

    private void visitInterfaceDeclaration(InterfaceDeclaration x, boolean annotation) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null)
            m = x.getDeclarationSpecifiers().size();
        if (m > 0) {
            printKeywordList(x.getDeclarationSpecifiers());
            m = 1;
        }
        if (x.getIdentifier() != null) {
            printElementIndentation(m, x);
            if (annotation)
                print("@");
            print("interface");
            printElement(1, x.getIdentifier());
        }
        if (x.getTypeParameters() != null && x.getTypeParameters().size() > 0) {
            print("<");
            printCommaList(x.getTypeParameters());
            print("> ");
        }
        if (x.getExtendedTypes() != null)
            printElement(1, x.getExtendedTypes());
        print(" {");
        if (x.getMembers() != null && !x.getMembers().isEmpty()) {
            printBlockList(2, 1, x.getMembers());
            changeLevel(-1);
        }
        printIndentation(1, getTotalIndentation());
        print(125);
        printFooter(x);
    }

    public void visitAnnotationDeclaration(AnnotationDeclaration x) {
        visitInterfaceDeclaration(x, true);
    }

    public void visitFieldDeclaration(FieldDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        printElement((m > 0) ? 1 : 0, x.getTypeReference());
        List<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null)
            printCommaList(0, 0, 1, varSpecs);
        print(59);
        printFooter(x);
    }

    public void visitLocalVariableDeclaration(LocalVariableDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        printElement((m > 0) ? 1 : 0, x.getTypeReference());
        List<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null)
            printCommaList(0, 0, 1, varSpecs);
        if (!(x.getStatementContainer() instanceof recoder.java.statement.LoopStatement))
            print(59);
        printFooter(x);
    }

    protected void visitVariableDeclaration(VariableDeclaration x) {
        visitVariableDeclaration(x, false);
    }

    protected void visitVariableDeclaration(VariableDeclaration x, boolean spec) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        printElement((m > 0) ? 1 : 0, x.getTypeReference());
        if (spec)
            print(" ...");
        List<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null)
            printCommaList(0, 0, 1, varSpecs);
        printFooter(x);
    }

    public void visitMethodDeclaration(MethodDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        if (x.getTypeParameters() != null && x.getTypeParameters().size() > 0) {
            if (m > 0) {
                print(32);
            } else {
                printElementIndentation(x);
            }
            print(60);
            printCommaList(x.getTypeParameters());
            print(62);
            m = 1;
        }
        if (x.getTypeReference() != null) {
            if (m > 0) {
                printElement(1, x.getTypeReference());
            } else {
                printElement(x.getTypeReference());
            }
            printElement(1, x.getIdentifier());
        } else if (m > 0) {
            printElement(1, x.getIdentifier());
        } else {
            printElement(x.getIdentifier());
        }
        if (getBooleanProperty("glueParameterLists")) {
            print(40);
        } else {
            print(" (");
        }
        if (x.getParameters() != null) {
            ASTList aSTList = x.getParameters();
            printCommaList(getBooleanProperty("glueParameters") ? 0 : 1, (List<? extends ProgramElement>) aSTList);
        }
        print(41);
        if (x.getThrown() != null)
            printElement(1, x.getThrown());
        if (x instanceof AnnotationPropertyDeclaration) {
            AnnotationPropertyDeclaration apd = (AnnotationPropertyDeclaration) x;
            Expression e = apd.getDefaultValueExpression();
            if (e != null) {
                print(" default ");
                e.accept(this);
            }
        }
        if (x.getBody() != null) {
            printElement(1, x.getBody());
        } else {
            print(59);
        }
        printFooter(x);
    }

    public void visitClassInitializer(ClassInitializer x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null) {
            m = x.getDeclarationSpecifiers().size();
            printKeywordList(x.getDeclarationSpecifiers());
        }
        if (x.getBody() != null)
            printElement((m > 0) ? 1 : 0, x.getBody());
        printFooter(x);
    }

    public void visitStatementBlock(StatementBlock x) {
        printHeader(x);
        printElementIndentation(x);
        print(123);
        boolean doNotPossiblyPrintIndentation = printContainerComments(x);
        if (x.getBody() != null && x.getBody().size() > 0) {
            printLineList(1, 1, x.getBody());
            changeLevel(-1);
            SourceElement.Position firstStatementEndPosition = x.getBody().get(0).getEndPosition();
            SourceElement.Position blockEndPosition = x.getEndPosition();
            if (x.getBody().size() > 1 || firstStatementEndPosition.equals(SourceElement.Position.UNDEFINED) || blockEndPosition.equals(SourceElement.Position.UNDEFINED) || firstStatementEndPosition.getLine() < blockEndPosition.getLine()) {
                printIndentation(1, getTotalIndentation());
            } else {
                printIndentation(0, blockEndPosition.getColumn() - firstStatementEndPosition.getColumn() - 1);
            }
        } else if (!doNotPossiblyPrintIndentation) {
            int lf = x.getEndPosition().getLine() - x.getStartPosition().getLine();
            if (lf > 0)
                printIndentation(lf, getIndentation());
        }
        print(125);
        printFooter(x);
    }

    public void visitBreak(Break x) {
        printHeader(x);
        printElementIndentation(x);
        print("break");
        if (x.getIdentifier() != null)
            printElement(1, x.getIdentifier());
        print(59);
        printFooter(x);
    }

    public void visitContinue(Continue x) {
        printHeader(x);
        printElementIndentation(x);
        print("continue");
        if (x.getIdentifier() != null)
            printElement(1, x.getIdentifier());
        print(59);
        printFooter(x);
    }

    public void visitReturn(Return x) {
        printHeader(x);
        printElementIndentation(x);
        print("return");
        if (x.getExpression() != null)
            printElement(1, x.getExpression());
        print(59);
        printFooter(x);
    }

    public void visitThrow(Throw x) {
        printHeader(x);
        printElementIndentation(x);
        print("throw");
        if (x.getExpression() != null)
            printElement(1, x.getExpression());
        print(59);
        printFooter(x);
    }

    public void visitDo(Do x) {
        printHeader(x);
        printElementIndentation(x);
        print("do");
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(59);
        } else if (getBooleanProperty("glueStatementBlocks")) {
            printElement(1, x.getBody());
        } else if (x.getBody() instanceof StatementBlock) {
            printElement(1, 0, x.getBody());
        } else {
            printElement(1, 1, 0, x.getBody());
            changeLevel(-1);
        }
        if (getBooleanProperty("glueStatementBlocks")) {
            print(" while");
        } else {
            printIndentation(1, getTotalIndentation());
            print("while");
        }
        if (getBooleanProperty("glueParameterLists")) {
            print(40);
        } else {
            print(" (");
        }
        if (x.getGuard() != null) {
            boolean glueExprParentheses = getBooleanProperty("glueExpressionParentheses");
            if (!glueExprParentheses)
                print(32);
            printElement(x.getGuard());
            if (!glueExprParentheses)
                print(32);
        }
        print(");");
        printFooter(x);
    }

    public void visitFor(For x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty("glueControlExpressions") ? "for(" : "for (");
        boolean glueExprParentheses = getBooleanProperty("glueExpressionParentheses");
        if (!glueExprParentheses)
            print(32);
        if (x.getInitializers() != null)
            printCommaList(x.getInitializers());
        print(59);
        if (x.getGuard() != null)
            printElement(1, x.getGuard());
        print(59);
        if (x.getUpdates() != null)
            printCommaList(0, 0, 1, x.getUpdates());
        if (!glueExprParentheses)
            print(32);
        print(41);
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(59);
        } else if (getBooleanProperty("glueStatementBlocks")) {
            printElement(1, x.getBody());
        } else if (x.getBody() instanceof StatementBlock) {
            printElement(1, 0, x.getBody());
        } else {
            printElement(1, 1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitEnhancedFor(EnhancedFor x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty("glueControlExpressions") ? "for(" : "for (");
        boolean glueExprParentheses = getBooleanProperty("glueExpressionParentheses");
        if (!glueExprParentheses)
            print(32);
        printCommaList(x.getInitializers());
        print(58);
        printElement(1, x.getGuard());
        if (!glueExprParentheses)
            print(32);
        print(41);
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(59);
        } else if (getBooleanProperty("glueStatementBlocks")) {
            printElement(1, x.getBody());
        } else {
            printElement(1, 1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitWhile(While x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty("glueControlExpressions") ? "while(" : "while (");
        boolean glueExpParentheses = getBooleanProperty("glueExpressionParentheses");
        if (!glueExpParentheses)
            print(32);
        if (x.getGuard() != null)
            printElement(x.getGuard());
        if (glueExpParentheses) {
            print(41);
        } else {
            print(" )");
        }
        if (x.getBody() == null || x.getBody() instanceof EmptyStatement) {
            print(59);
        } else if (getBooleanProperty("glueStatementBlocks")) {
            printElement(1, x.getBody());
        } else if (x.getBody() instanceof StatementBlock) {
            printElement(1, 0, x.getBody());
        } else {
            printElement(1, 1, 0, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitAssert(Assert x) {
        printHeader(x);
        printElementIndentation(x);
        print("assert");
        if (x.getCondition() != null)
            printElement(1, x.getCondition());
        if (x.getMessage() != null) {
            print(" :");
            printElement(1, x.getMessage());
        }
        print(59);
        printFooter(x);
    }

    public void visitIf(If x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty("glueControlExpressions") ? "if(" : "if (");
        boolean glueExpr = getBooleanProperty("glueExpressionParentheses");
        if (x.getExpression() != null)
            if (glueExpr) {
                printElement(x.getExpression());
            } else {
                printElement(1, x.getExpression());
            }
        if (glueExpr) {
            print(41);
        } else {
            print(" )");
        }
        if (x.getThen() != null)
            if (getBooleanProperty("glueStatementBlocks")) {
                printElement(1, x.getThen());
            } else if (x.getThen().getBody() instanceof StatementBlock) {
                printElement(1, 0, x.getThen());
            } else {
                printElement(1, 1, 0, x.getThen());
                changeLevel(-1);
            }
        if (x.getElse() != null)
            if (getBooleanProperty("glueSequentialBranches")) {
                printElement(1, x.getElse());
            } else {
                printElement(1, 0, x.getElse());
            }
        printFooter(x);
    }

    public void visitSwitch(Switch x) {
        printHeader(x);
        printElementIndentation(x);
        print("switch (");
        if (x.getExpression() != null)
            printElement(x.getExpression());
        print(") {");
        if (x.getBranchList() != null)
            if (getBooleanProperty("glueSequentialBranches")) {
                printLineList(1, 1, x.getBranchList());
                changeLevel(-1);
            } else {
                printLineList(1, 0, x.getBranchList());
            }
        printIndentation(1, getTotalIndentation());
        print(125);
        printFooter(x);
    }

    public void visitTry(Try x) {
        printHeader(x);
        printElementIndentation(x);
        print("try");
        if (x.getBody() != null)
            if (getBooleanProperty("glueStatementBlocks")) {
                printElement(1, x.getBody());
            } else {
                printElement(1, 0, x.getBody());
            }
        if (x.getBranchList() != null)
            if (getBooleanProperty("glueSequentialBranches")) {
                for (int i = 0; i < x.getBranchList().size(); i++)
                    printElement(1, x.getBranchList().get(i));
            } else {
                printLineList(1, 0, x.getBranchList());
            }
        printFooter(x);
    }

    public void visitLabeledStatement(LabeledStatement x) {
        printHeader(x);
        if (x.getIdentifier() != null) {
            printElement(x.getIdentifier());
            printElementIndentation(x);
            print(58);
        }
        if (x.getBody() != null)
            printElement(1, 0, x.getBody());
        printFooter(x);
    }

    public void visitSynchronizedBlock(SynchronizedBlock x) {
        printHeader(x);
        printElementIndentation(x);
        print("synchronized");
        if (x.getExpression() != null) {
            print(40);
            printElement(x.getExpression());
            print(41);
        }
        if (x.getBody() != null)
            printElement(1, x.getBody());
        printFooter(x);
    }

    public void visitImport(Import x) {
        printHeader(x);
        printElementIndentation(x);
        print("import");
        if (x.isStaticImport())
            print(" static");
        printElement(1, x.getReference());
        if (x.isMultiImport()) {
            print(".*;");
        } else {
            if (x.isStaticImport()) {
                print(".");
                printElement(x.getStaticIdentifier());
            }
            print(59);
        }
        printFooter(x);
    }

    public void visitUncollatedReferenceQualifier(UncollatedReferenceQualifier x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(46);
        }
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        printFooter(x);
    }

    public void visitExtends(Extends x) {
        printHeader(x);
        if (x.getSupertypes() != null) {
            printElementIndentation(x);
            print("extends");
            printCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void visitImplements(Implements x) {
        printHeader(x);
        if (x.getSupertypes() != null) {
            printElementIndentation(x);
            print("implements");
            printCommaList(0, 0, 1, x.getSupertypes());
        }
        printFooter(x);
    }

    public void visitVariableSpecification(VariableSpecification x) {
        printHeader(x);
        printElement(x.getIdentifier());
        for (int i = 0; i < x.getDimensions(); i++)
            print("[]");
        if (x.getInitializer() != null) {
            print(" = ");
            printElement(0, 0, 1, x.getInitializer());
        }
        printFooter(x);
    }

    public void visitBinaryAnd(BinaryAnd x) {
        printHeader(x);
        printOperator(x, "&");
        printFooter(x);
    }

    public void visitBinaryAndAssignment(BinaryAndAssignment x) {
        printHeader(x);
        printOperator(x, "&=");
        printFooter(x);
    }

    public void visitBinaryOrAssignment(BinaryOrAssignment x) {
        printHeader(x);
        printOperator(x, "|=");
        printFooter(x);
    }

    public void visitBinaryXOrAssignment(BinaryXOrAssignment x) {
        printHeader(x);
        printOperator(x, "^=");
        printFooter(x);
    }

    public void visitCopyAssignment(CopyAssignment x) {
        printHeader(x);
        printOperator(x, "=");
        printFooter(x);
    }

    public void visitDivideAssignment(DivideAssignment x) {
        printHeader(x);
        printOperator(x, "/=");
        printFooter(x);
    }

    public void visitMinusAssignment(MinusAssignment x) {
        printHeader(x);
        printOperator(x, "-=");
        printFooter(x);
    }

    public void visitModuloAssignment(ModuloAssignment x) {
        printHeader(x);
        printOperator(x, "%=");
        printFooter(x);
    }

    public void visitPlusAssignment(PlusAssignment x) {
        printHeader(x);
        printOperator(x, "+=");
        printFooter(x);
    }

    public void visitPostDecrement(PostDecrement x) {
        printHeader(x);
        printOperator(x, "--");
        printFooter(x);
    }

    public void visitPostIncrement(PostIncrement x) {
        printHeader(x);
        printOperator(x, "++");
        printFooter(x);
    }

    public void visitPreDecrement(PreDecrement x) {
        printHeader(x);
        printOperator(x, "--");
        printFooter(x);
    }

    public void visitPreIncrement(PreIncrement x) {
        printHeader(x);
        printOperator(x, "++");
        printFooter(x);
    }

    public void visitShiftLeftAssignment(ShiftLeftAssignment x) {
        printHeader(x);
        printOperator(x, "<<=");
        printFooter(x);
    }

    public void visitShiftRightAssignment(ShiftRightAssignment x) {
        printHeader(x);
        printOperator(x, ">>=");
        printFooter(x);
    }

    public void visitTimesAssignment(TimesAssignment x) {
        printHeader(x);
        printOperator(x, "*=");
        printFooter(x);
    }

    public void visitUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {
        printHeader(x);
        printOperator(x, ">>>=");
        printFooter(x);
    }

    public void visitBinaryNot(BinaryNot x) {
        printHeader(x);
        printOperator(x, "~");
        printFooter(x);
    }

    public void visitBinaryOr(BinaryOr x) {
        printHeader(x);
        printOperator(x, "|");
        printFooter(x);
    }

    public void visitBinaryXOr(BinaryXOr x) {
        printHeader(x);
        printOperator(x, "^");
        printFooter(x);
    }

    public void visitConditional(Conditional x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (x.getArguments() != null) {
            if (addParentheses)
                print(40);
            printElement(0, x.getArguments().get(0));
            print(" ?");
            printElement(1, x.getArguments().get(1));
            print(" :");
            printElement(1, x.getArguments().get(2));
            if (addParentheses)
                print(41);
        }
        printFooter(x);
    }

    public void visitDivide(Divide x) {
        printHeader(x);
        printOperator(x, "/");
        printFooter(x);
    }

    public void visitEquals(Equals x) {
        printHeader(x);
        printOperator(x, "==");
        printFooter(x);
    }

    public void visitGreaterOrEquals(GreaterOrEquals x) {
        printHeader(x);
        printOperator(x, ">=");
        printFooter(x);
    }

    public void visitGreaterThan(GreaterThan x) {
        printHeader(x);
        printOperator(x, ">");
        printFooter(x);
    }

    public void visitLessOrEquals(LessOrEquals x) {
        printHeader(x);
        printOperator(x, "<=");
        printFooter(x);
    }

    public void visitLessThan(LessThan x) {
        printHeader(x);
        printOperator(x, "<");
        printFooter(x);
    }

    public void visitNotEquals(NotEquals x) {
        printHeader(x);
        printOperator(x, "!=");
        printFooter(x);
    }

    public void visitNewArray(NewArray x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses)
            print(40);
        printElementIndentation(x);
        print("new");
        printElement(1, x.getTypeReference());
        int i = 0;
        if (x.getArguments() != null)
            for (; i < x.getArguments().size(); i++) {
                print(91);
                printElement(x.getArguments().get(i));
                print(93);
            }
        for (; i < x.getDimensions(); i++)
            print("[]");
        if (x.getArrayInitializer() != null)
            printElement(1, x.getArrayInitializer());
        if (addParentheses)
            print(41);
        printFooter(x);
    }

    public void visitInstanceof(Instanceof x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses)
            print(40);
        if (x.getArguments() != null)
            printElement(0, x.getArguments().get(0));
        printElementIndentation(1, x);
        print("instanceof");
        if (x.getTypeReference() != null)
            printElement(1, x.getTypeReference());
        if (addParentheses)
            print(41);
        printFooter(x);
    }

    public void visitNew(New x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses)
            print(40);
        if (x.getReferencePrefix() != null) {
            printElement(0, x.getReferencePrefix());
            print(46);
        }
        printElementIndentation(x);
        print("new");
        printElement(1, x.getTypeReference());
        if (getBooleanProperty("glueParameterLists")) {
            print(40);
        } else {
            print(" (");
        }
        if (x.getArguments() != null)
            printCommaList(x.getArguments());
        print(41);
        if (x.getClassDeclaration() != null)
            printElement(1, x.getClassDeclaration());
        if (addParentheses)
            print(41);
        if (x.getStatementContainer() != null)
            print(59);
        printFooter(x);
    }

    public void visitTypeCast(TypeCast x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses)
            print(40);
        printElementIndentation(x);
        print(40);
        if (x.getTypeReference() != null)
            printElement(0, x.getTypeReference());
        print(41);
        if (x.getArguments() != null)
            printElement(0, x.getArguments().get(0));
        if (addParentheses)
            print(41);
        printFooter(x);
    }

    public void visitLogicalAnd(LogicalAnd x) {
        printHeader(x);
        printOperator(x, "&&");
        printFooter(x);
    }

    public void visitLogicalNot(LogicalNot x) {
        printHeader(x);
        printOperator(x, "!");
        printFooter(x);
    }

    public void visitLogicalOr(LogicalOr x) {
        printHeader(x);
        printOperator(x, "||");
        printFooter(x);
    }

    public void visitMinus(Minus x) {
        printHeader(x);
        printOperator(x, "-");
        printFooter(x);
    }

    public void visitModulo(Modulo x) {
        printHeader(x);
        printOperator(x, "%");
        printFooter(x);
    }

    public void visitNegative(Negative x) {
        printHeader(x);
        printOperator(x, "-");
        printFooter(x);
    }

    public void visitPlus(Plus x) {
        printHeader(x);
        printOperator(x, "+");
        printFooter(x);
    }

    public void visitPositive(Positive x) {
        printHeader(x);
        printOperator(x, "+");
        printFooter(x);
    }

    public void visitShiftLeft(ShiftLeft x) {
        printHeader(x);
        printOperator(x, "<<");
        printFooter(x);
    }

    public void visitShiftRight(ShiftRight x) {
        printHeader(x);
        printOperator(x, ">>");
        printFooter(x);
    }

    public void visitTimes(Times x) {
        printHeader(x);
        printOperator(x, "*");
        printFooter(x);
    }

    public void visitUnsignedShiftRight(UnsignedShiftRight x) {
        printHeader(x);
        printOperator(x, ">>>");
        printFooter(x);
    }

    public void visitArrayReference(ArrayReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null)
            printElement(x.getReferencePrefix());
        if (x.getDimensionExpressions() != null) {
            int s = x.getDimensionExpressions().size();
            for (int i = 0; i < s; i++) {
                print(91);
                printElement(x.getDimensionExpressions().get(i));
                print(93);
            }
        }
        printFooter(x);
    }

    public void visitFieldReference(FieldReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(46);
        }
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        printFooter(x);
    }

    public void visitVariableReference(VariableReference x) {
        printHeader(x);
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        printFooter(x);
    }

    public void visitMetaClassReference(MetaClassReference x) {
        printHeader(x);
        if (x.getTypeReference() != null) {
            printElement(x.getTypeReference());
            printElementIndentation(x);
            print(46);
        }
        print("class");
        printFooter(x);
    }

    public void visitMethodReference(MethodReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            print(46);
        }
        if (x.getTypeArguments() != null && x.getTypeArguments().size() > 0) {
            print(60);
            printCommaList(x.getTypeArguments());
            print(62);
        }
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        if (getBooleanProperty("glueParameterLists")) {
            print(40);
        } else {
            print(" (");
        }
        if (x.getArguments() != null)
            printCommaList(x.getArguments());
        print(41);
        if (x.getStatementContainer() != null)
            print(59);
        printFooter(x);
    }

    public void visitSuperConstructorReference(SuperConstructorReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            print(46);
        }
        printElementIndentation(x);
        if (getBooleanProperty("glueParameterLists")) {
            print("super(");
        } else {
            print("super (");
        }
        if (x.getArguments() != null)
            printCommaList(x.getArguments());
        print(");");
        printFooter(x);
    }

    public void visitThisConstructorReference(ThisConstructorReference x) {
        printHeader(x);
        printElementIndentation(x);
        print(getBooleanProperty("glueParameterLists") ? "this(" : "this (");
        if (x.getArguments() != null)
            printCommaList(x.getArguments());
        print(");");
        printFooter(x);
    }

    public void visitSuperReference(SuperReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(".super");
        } else {
            printElementIndentation(x);
            print("super");
        }
        printFooter(x);
    }

    public void visitThisReference(ThisReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            printElementIndentation(x);
            print(".this");
        } else {
            printElementIndentation(x);
            print("this");
        }
        printFooter(x);
    }

    public void visitArrayLengthReference(ArrayLengthReference x) {
        printHeader(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            print(46);
        }
        printElementIndentation(x);
        print("length");
        printFooter(x);
    }

    public void visitThen(Then x) {
        printHeader(x);
        if (x.getBody() != null)
            printElement(x.getBody());
        printFooter(x);
    }

    public void visitElse(Else x) {
        printHeader(x);
        printElementIndentation(x);
        print("else");
        if (x.getBody() != null)
            if (getBooleanProperty("glueStatementBlocks")) {
                printElement(1, x.getBody());
            } else if (x.getBody() instanceof StatementBlock) {
                printElement(1, 0, x.getBody());
            } else {
                printElement(1, 1, 0, x.getBody());
                changeLevel(-1);
            }
        printFooter(x);
    }

    public void visitCase(Case x) {
        printHeader(x);
        printElementIndentation(x);
        print("case");
        if (x.getExpression() != null)
            printElement(1, x.getExpression());
        print(58);
        if (x.getBody() != null && x.getBody().size() > 0) {
            printLineList(1, 1, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitCatch(Catch x) {
        printHeader(x);
        if (getBooleanProperty("glueControlExpressions")) {
            printElementIndentation(x);
            print("catch(");
        } else {
            printElementIndentation(x);
            print("catch (");
        }
        if (x.getParameterDeclaration() != null)
            printElement(x.getParameterDeclaration());
        print(41);
        if (x.getBody() != null)
            printElement(1, x.getBody());
        printFooter(x);
    }

    public void visitDefault(Default x) {
        printHeader(x);
        printElementIndentation(x);
        print("default:");
        if (x.getBody() != null && x.getBody().size() > 0) {
            printLineList(1, 1, x.getBody());
            changeLevel(-1);
        }
        printFooter(x);
    }

    public void visitFinally(Finally x) {
        printHeader(x);
        printElementIndentation(x);
        print("finally");
        if (x.getBody() != null)
            printElement(1, x.getBody());
        printFooter(x);
    }

    public void visitAbstract(Abstract x) {
        printHeader(x);
        printElementIndentation(x);
        print("abstract");
        printFooter(x);
    }

    public void visitFinal(Final x) {
        printHeader(x);
        printElementIndentation(x);
        print("final");
        printFooter(x);
    }

    public void visitNative(Native x) {
        printHeader(x);
        printElementIndentation(x);
        print("native");
        printFooter(x);
    }

    public void visitPrivate(Private x) {
        printHeader(x);
        printElementIndentation(x);
        print("private");
        printFooter(x);
    }

    public void visitProtected(Protected x) {
        printHeader(x);
        printElementIndentation(x);
        print("protected");
        printFooter(x);
    }

    public void visitPublic(Public x) {
        printHeader(x);
        printElementIndentation(x);
        print("public");
        printFooter(x);
    }

    public void visitStatic(Static x) {
        printHeader(x);
        printElementIndentation(x);
        print("static");
        printFooter(x);
    }

    public void visitStrictFp(StrictFp x) {
        printHeader(x);
        printElementIndentation(x);
        print("strictfp");
        printFooter(x);
    }

    public void visitSynchronized(Synchronized x) {
        printHeader(x);
        printElementIndentation(x);
        print("synchronized");
        printFooter(x);
    }

    public void visitTransient(Transient x) {
        printHeader(x);
        printElementIndentation(x);
        print("transient");
        printFooter(x);
    }

    public void visitVolatile(Volatile x) {
        printHeader(x);
        printElementIndentation(x);
        print("volatile");
        printFooter(x);
    }

    public void visitAnnotationUse(AnnotationUseSpecification a) {
        printHeader(a);
        printElementIndentation(a);
        print(64);
        printElement(a.getTypeReference());
        ASTList aSTList = a.getElementValuePairs();
        if (aSTList != null) {
            print(40);
            printCommaList(0, 0, 0, (List<? extends ProgramElement>) aSTList);
            print(41);
        }
        printFooter(a);
    }

    public void visitElementValuePair(AnnotationElementValuePair x) {
        printHeader(x);
        printElementIndentation(x);
        AnnotationPropertyReference id = x.getElement();
        if (id != null) {
            printElement(id);
            print(" =");
        }
        ProgramElement ev = x.getElementValue();
        if (ev != null)
            printElement(ev);
        printFooter(x);
    }

    public void visitAnnotationPropertyReference(AnnotationPropertyReference x) {
        printHeader(x);
        printElementIndentation(x);
        Identifier id = x.getIdentifier();
        if (id != null)
            printElement(id);
        printFooter(x);
    }

    public void visitEmptyStatement(EmptyStatement x) {
        printHeader(x);
        printElementIndentation(x);
        print(59);
        printFooter(x);
    }

    public void visitComment(Comment x) {
        printElementIndentation(x);
        print(x.getText());
        if (this.overwriteParsePositions) {
            this.overwritePosition.setPosition(this.line, Math.max(0, this.column - 1));
            x.getLastElement().setEndPosition(this.overwritePosition);
        }
    }

    public void visitParenthesizedExpression(ParenthesizedExpression x) {
        printHeader(x);
        printElementIndentation(x);
        print(40);
        if (x.getArguments() != null)
            printElement(x.getArguments().get(0));
        print(41);
        printFooter(x);
    }

    public void visitEnumConstructorReference(EnumConstructorReference x) {
        printHeader(x);
        printElementIndentation(x);
        ASTList aSTList = x.getArguments();
        if (aSTList != null) {
            print(40);
            printCommaList((List<? extends ProgramElement>) aSTList);
            print(41);
        }
        if (x.getClassDeclaration() != null)
            printElement(x.getClassDeclaration());
    }

    public void visitEnumConstantDeclaration(EnumConstantDeclaration x) {
        printHeader(x);
        printElementIndentation(x);
        if (x.getAnnotations() != null && x.getAnnotations().size() != 0) {
            printKeywordList(x.getAnnotations());
            print(32);
        }
        printElement(1, x.getEnumConstantSpecification());
        printFooter(x);
    }

    public void visitEnumConstantSpecification(EnumConstantSpecification x) {
        printHeader(x);
        printElement(x.getIdentifier());
        printElement(x.getConstructorReference());
        printFooter(x);
    }

    public void visitEnumDeclaration(EnumDeclaration x) {
        printHeader(x);
        int m = 0;
        if (x.getDeclarationSpecifiers() != null)
            m = x.getDeclarationSpecifiers().size();
        if (m > 0) {
            printKeywordList(x.getDeclarationSpecifiers());
            m = 1;
        }
        printElementIndentation(m, x);
        print("enum");
        printElement(1, x.getIdentifier());
        print(32);
        print(123);
        printContainerComments(x);
        printCommaList(2, 1, 1, x.getConstants());
        print(";");
        changeLevel(-1);
        printBlockList(2, 1, x.getNonConstantMembers());
        changeLevel(-1);
        printIndentation(1, getTotalIndentation());
        print(125);
        printFooter(x);
    }

    public void visitTypeArgument(TypeArgumentDeclaration x) {
        printHeader(x);
        switch (x.getWildcardMode()) {
            case Any:
                print("?");
                break;
            case Extends:
                print("? extends ");
                break;
            case Super:
                print("? super ");
                break;
        }
        if (x.getTypeReferenceCount() == 1)
            printElement(x.getTypeReferenceAt(0));
        printFooter(x);
    }

    public void visitTypeParameter(TypeParameterDeclaration x) {
        printHeader(x);
        if (x.getIdentifier() != null)
            printElement(x.getIdentifier());
        if (x.getBounds() != null && x.getBounds().size() != 0) {
            print(" extends ");
            printProgramElementList(0, 0, 0, "&", 0, 1, x.getBounds());
        }
        printFooter(x);
    }

    public void visitParameterDeclaration(ParameterDeclaration x) {
        visitVariableDeclaration(x, x.isVarArg());
    }
}
