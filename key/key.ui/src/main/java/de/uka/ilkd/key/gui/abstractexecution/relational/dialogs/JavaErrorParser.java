// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.abstractexecution.relational.dialogs;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import javax.swing.text.BadLocationException;
import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaCompiler.CompilationTask;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import org.fife.ui.rsyntaxtextarea.RSyntaxDocument;
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult;
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice;
import org.fife.ui.rsyntaxtextarea.parser.ParseResult;

import de.uka.ilkd.key.gui.abstractexecution.relational.model.ProgramVariableDeclaration;

/**
 * @author Dominic Steinhoefel
 *
 */
public class JavaErrorParser extends AbstractParser {
    private final Set<ProgramVariableDeclaration> progVarDecls = new HashSet<>();

    public void setProgVarDecls(Collection<ProgramVariableDeclaration> progVarDecls) {
        this.progVarDecls.clear();
        this.progVarDecls.addAll(progVarDecls);
    }

    @Override
    public ParseResult parse(RSyntaxDocument doc, String style) {
        final DefaultParseResult result = new DefaultParseResult(this);

        List<Diagnostic<? extends JavaFileObject>> diagnostics = null;
        Path tempFile = null;
        try {
            tempFile = Files.createTempFile("AERelational_", ".java");
            tempFile.toFile().deleteOnExit();
            String className = tempFile.getFileName().toString();
            className = className.substring(0, className.length() - 5);
            final String javaDoc = createDocument(className, doc.getText(0, doc.getLength()));
            diagnostics = compile(tempFile, javaDoc);

            final int javaDocBoilerplateLineLength = javaDoc.indexOf('\n') + 1;

            for (Diagnostic<?> diagnostic : diagnostics) {
                final int line = (int) diagnostic.getLineNumber() - 1;
                int startPos = (int) diagnostic.getStartPosition() - javaDocBoilerplateLineLength;
                int length = (int) (diagnostic.getEndPosition() - diagnostic.getStartPosition());
                if (length == 0 && startPos > 0) {
                    startPos--;
                    length = 1;
                }

                result.addNotice(new DefaultParserNotice( //
                        this, diagnostic.getMessage(null), line, startPos, length));
            }

        } catch (IOException e) {
            return result;
        } catch (BadLocationException e) {
            // This should not happen!
            e.printStackTrace();
            return result;
        }

        return result;
    }

    private List<Diagnostic<? extends JavaFileObject>> compile(final Path file,
            final String javaClassCode) throws IOException {
        Files.write(file, javaClassCode.getBytes());

        final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

        if (compiler == null) {
            return Collections.emptyList();
        }

        final DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<JavaFileObject>();
        final StandardJavaFileManager fileManager = //
                compiler.getStandardFileManager(diagnostics, null, null);
        final Iterable<? extends JavaFileObject> units = //
                fileManager.getJavaFileObjects(file.toFile());
        final CompilationTask task = compiler.getTask( //
                null, fileManager, diagnostics, null, null, units);
        task.call();
        fileManager.close();

        return diagnostics.getDiagnostics();
    }

    private String createDocument(final String className, String body) {
        body = replaceAbstractExpression(body);
        body = replaceAbstractStatement(body);

        final StringBuilder sb = new StringBuilder();
        sb.append("public class ");
        sb.append(className);
        sb.append("{");
        sb.append("public Object method(");
        sb.append(progVarDecls.stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(", ")));
        sb.append(") {");
        sb.append("\n");
        sb.append(body);
        sb.append("\n");
        sb.append("}");
        sb.append("}");
        return sb.toString();
    }

    private String replaceAbstractStatement(final String body) {
        final Pattern asPattern = Pattern.compile("\\\\abstract_statement +[a-zA-Z0-9_.]+ *;");
        final Matcher asMatcher = asPattern.matcher(body);

        String newBody = body;
        while (asMatcher.find()) {
            final String match = asMatcher.group();
            newBody = newBody.replaceAll(Pattern.quote(match),
                    String.format("%1$-" + match.length() + "s", ";"));
        }

        return newBody;
    }

    private String replaceAbstractExpression(final String body) {
        final Pattern aexpPattern = Pattern
                .compile("\\\\abstract_expression +([a-zA-Z0-9_.]+) +[a-zA-Z0-9_.]+");
        final Matcher aexpMatcher = aexpPattern.matcher(body);

        String newBody = body;
        while (aexpMatcher.find()) {
            final String match = aexpMatcher.group();

            final String type = aexpMatcher.group(1);
            String replacement = "null";
            if (type.equals("boolean")) {
                replacement = "true";
            } else if (type.equals("int") || type.equals("char") || type.equals("long")) {
                replacement = "0";
            }

            newBody = newBody.replaceAll(Pattern.quote(match),
                    String.format("%1$-" + match.length() + "s", replacement));
        }

        return newBody;
    }

}
