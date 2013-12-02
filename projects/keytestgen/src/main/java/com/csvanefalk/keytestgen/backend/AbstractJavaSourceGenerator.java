package com.csvanefalk.keytestgen.backend;

/**
 * Base class for KeYTestGen backend modules generating Java code for various
 * test frameworks. Provides essential utility methods and formatting constants.
 *
 * @author christopher
 */
public abstract class AbstractJavaSourceGenerator {

    /**
     * A newline
     */
    protected static final String NEWLINE = "\n";

    /**
     * 4-space tab
     */
    protected static final String TAB = "    ";

    /**
     * Indentation counter, for keeping tabs on how many tabs (hah!) should be
     * prefixed to each line.
     */
    private int indentation = 0;

    /**
     * Used for constructing the final output String.
     */
    private final StringBuilder output = new StringBuilder();

    protected void appendToOutput(final String text) {
        output.append(text);
    }

    protected void decreaseIndentation() {
        --indentation;
    }

    protected String getCurrentOutput() {
        return output.toString();
    }

    protected void increaseIndentation() {
        ++indentation;
    }

    /**
     * Inserts a number of tabs according to the current indentation level of
     * the text.
     */
    protected void indent() {

        for (int i = 0; i < indentation; i++) {
            output.append(AbstractJavaSourceGenerator.TAB);
        }
    }

    /**
     * Writes the signature head of a Java class declaration with the canonical
     * form:
     * <p/>
     * <pre>
     * <code>[{@literal @annotation}]
     * <code>[access] [modifiers] Type Name([parameters])</code>
     * </pre>
     * <p/>
     * where [{@literal @annotation}] is empty, or a set of valid Java
     * annotations.
     * <p/>
     * where [access] is empty, or exactly one of the following:
     * <p/>
     * <pre>
     * <code>public, protected, private</code>
     * </pre>
     * <p/>
     * where [modifier] is empty, or a set containing at most 1 of the
     * following:
     * <p/>
     * <pre>
     * <code>final, abstract</code>
     * </pre>
     * <p/>
     * Declaring a method opens a new scope, and hence increases the indentation
     * level for the text.
     *
     * @param visibility the [access] for the class
     * @param modifier   the [modifiers] for the class
     * @param name       the Name for the class
     */
    protected void writeClassHeader(final String[] annotations,
                                    final String visibility, final String modifier, final String name) {

        if (annotations != null) {
            for (final String annotation : annotations) {
                writeIndentedLine(annotation
                        + AbstractJavaSourceGenerator.NEWLINE);
            }
        }

        indent();

        output.append(visibility + " ");
        output.append(modifier + " ");
        output.append("class" + " ");
        output.append(name);
        output.append(" {\n");

        increaseIndentation();
    }

    /**
     * Writes a closing brace ("}") to the Java source file. This will decrease
     * the indentation level for the text.
     */
    protected void writeClosingBrace() {

        decreaseIndentation();
        indent();
        output.append("}\n");
    }

    /**
     * Writes a nested Java comment.
     *
     * @param text text of comment
     */
    protected void writeComment(final String text, final boolean isJavadoc) {

        writeIndentedLine(AbstractJavaSourceGenerator.NEWLINE);

        if (isJavadoc) {
            writeIndentedLine("/**\n");
        } else {
            writeIndentedLine("/*\n");
        }

        final String[] words = text.split(" ");

        writeIndentedLine(" *");
        int characterCount = 0;
        for (final String word : words) {

            if (word.trim().isEmpty()) {
                continue;
            }

            if (characterCount >= 50) {
                characterCount = 0;
                output.append(" " + word + AbstractJavaSourceGenerator.NEWLINE);
                writeIndentedLine(" *");
                continue;
            } else {
                output.append(" " + word);
                characterCount += word.length();
            }
        }
        output.append(AbstractJavaSourceGenerator.NEWLINE);

        writeIndentedLine(" */\n");
    }

    /**
     * Writes an indented line of text to the Java source file.
     *
     * @param text the text to write
     */
    protected void writeIndentedLine(final String text) {

        indent();
        output.append(text);
    }

    protected void writeLine(final Object obj) {

        indent();
        output.append(obj.toString());
    }

    /**
     * Writes the signature head of a Java method declaration with the canonical
     * form:
     * <p/>
     * <pre>
     * <code>[{@literal @annotation}]</code>
     * <code>[access] [modifiers] Type Name([parameters])</code>
     * </pre>
     * <p/>
     * where [{@literal @annotation}] is empty, or a set of valid Java
     * annotations.
     * <p/>
     * where [access] is empty, or exactly one of the following:
     * <p/>
     * <pre>
     * <code>public, protected, private</code>
     * </pre>
     * <p/>
     * where [modifier] is empty, or a set containing at most 1 of each of the
     * following:
     * <p/>
     * <pre>
     * <code>static, final, native, abstract</code>
     * </pre>
     * <p/>
     * where Type is a reference or primitive Java type, Name is a legitimate
     * Java identifier, and where [parameters] is either empty, or a set of
     * bounded size consisting of elements with the following form:
     * <p/>
     * <pre>
     * <code>[modifier] Type Name</code>
     * </pre>
     * <p/>
     * Where [modifier] is either empty or the element <code>final</code>, Type
     * is a valid Java type, and Name is a valid Java identifier.
     * <p/>
     * Declaring a method opens a new scope, and hence increases the indentation
     * level for the text.
     *
     * @param annotations the [annotations] for the method
     * @param visibility  the [access] for the method
     * @param returnType  the Type for the method
     * @param modifiers   the [modifiers] for the method
     * @param name        the Name for the method
     */
    protected void writeMethodHeader(final String[] annotations,
                                     final String visibility, final String[] modifiers,
                                     final String returnType, final String name,
                                     final String[] parameters, final String[] exceptions) {

        if (annotations != null) {
            for (final String annotation : annotations) {
                writeIndentedLine(annotation
                        + AbstractJavaSourceGenerator.NEWLINE);
            }
        }

        indent();

		/*
         * Write the visibility modifier of the method
		 */
        output.append(visibility + " ");

		/*
         * Write the modifiers, if any.
		 */
        if ((modifiers != null) && (modifiers.length != 0)) {
            for (final String modifier : modifiers) {
                output.append(modifier + " ");
            }
        }

        output.append(returnType + " ");

        output.append(name + " ");

		/*
         * Write the parameters for the method, if any.
		 */
        output.append("(");
        if ((parameters != null) && (parameters.length != 0)) {
            for (int i = 0; i < parameters.length; i++) {
                final String parameter = parameters[i];
                if (i < (parameters.length - 1)) {
                    output.append(parameter + ", ");
                } else {
                    output.append(parameter);
                }
            }
        }
        output.append(")");

		/*
		 * Write the exceptions, if any.
		 */
        if (exceptions != null) {
            output.append(AbstractJavaSourceGenerator.NEWLINE);
            indent();

            writeIndentedLine("throws ");
            for (int i = 0; i < exceptions.length; i++) {
                final String exception = exceptions[i];
                output.append(exception);
                if (i != (exceptions.length - 1)) {
                    output.append(", ");
                }
            }
        }

		/*
		 * Close the method header.
		 */
        output.append(" {\n");
        increaseIndentation();
    }

    protected void writeNewLine() {
        writeIndentedLine(AbstractJavaSourceGenerator.NEWLINE);
    }

    /**
     * Writes an opening brace ("{") to the Java source file. This will increase
     * the indentation level for the text.
     */
    protected void writeOpeningBrace() {

        indent();
        increaseIndentation();
        output.append("{\n");
    }

    protected void writeUnindentedLine(final Object obj) {
        output.append(obj.toString());
    }

    protected void writeUnindentedLine(final String text) {
        output.append(text);
    }
}