package de.uka.ilkd.key.testgeneration.backend;

/**
 * Base class for KeYTestGen backend modules generating Java code for various
 * test frameworks. Provides essential utility methods and formatting constants.
 * 
 * @author christopher
 * 
 */
public abstract class AbstractJavaSourceGenerator {

    // 4-space tab
    private static final String TAB = "    ";

    private int indentation = 0;

    private StringBuilder output = new StringBuilder();

    /**
     * Writes the signature head of a Java class declaration with the canonical
     * form:
     * 
     * <pre>
     * <code>[{@literal @annotation}]
     * <code>[access] [modifiers] Type Name([parameters])</code>
     * </pre>
     * 
     * where [{@literal @annotation}] is empty, or a set of valid Java
     * annotations.
     * 
     * where [access] is empty, or exactly one of the following:
     * 
     * <pre>
     * <code>public, protected, private</code>
     * </pre>
     * 
     * where [modifier] is empty, or a set containing at most 1 of the
     * following:
     * 
     * <pre>
     * <code>final, abstract</code>
     * </pre>
     * 
     * Declaring a method opens a new scope, and hence increases the indentation
     * level for the text.
     * 
     * @param visibility
     *            the [access] for the class
     * @param modifier
     *            the [modifiers] for the class
     * @param name
     *            the Name for the class
     */
    protected void writeClassHeader(String[] annotations, String visibility,
            String modifier, String name) {

        if (annotations != null) {
            for (String annotation : annotations) {
                writeLine(annotation);
            }
        }

        indent();

        output.append(visibility);
        output.append(modifier);
        output.append("class");
        output.append(name);
        output.append(" {");

        indentation++;
    }

    /**
     * Writes the signature head of a Java method declaration with the canonical
     * form:
     * 
     * <pre>
     * <code>[{@literal @annotation}]</code>
     * <code>[access] [modifiers] Type Name([parameters])</code>
     * </pre>
     * 
     * where [{@literal @annotation}] is empty, or a set of valid Java
     * annotations.
     * <p>
     * where [access] is empty, or exactly one of the following:
     * 
     * <pre>
     * <code>public, protected, private</code>
     * </pre>
     * 
     * where [modifier] is empty, or a set containing at most 1 of each of the
     * following:
     * 
     * <pre>
     * <code>static, final, native, abstract</code>
     * </pre>
     * 
     * where Type is a reference or primitive Java type, Name is a legitimate
     * Java identifier, and where [parameters] is either empty, or a set of
     * bounded size consisting of elements with the following form:
     * 
     * <pre>
     * <code>[modifier] Type Name</code>
     * </pre>
     * 
     * Where [modifier] is either empty or the element <code>final</code>, Type
     * is a valid Java type, and Name is a valid Java identifier.
     * <p>
     * Declaring a method opens a new scope, and hence increases the indentation
     * level for the text.
     * 
     * @param annotations
     *            the [annotations] for the method
     * @param visibility
     *            the [access] for the method
     * @param returnType
     *            the Type for the method
     * @param modifiers
     *            the [modifiers] for the method
     * @param name
     *            the Name for the method
     */
    protected void writeMethodHeader(String[] annotations, String visibility,
            String[] modifiers, String returnType, String name,
            String[] parameters) {

        if (annotations != null) {
            for (String annotation : annotations) {
                writeLine(annotation);
            }
        }

        indent();

        output.append(visibility + " ");

        for (String modifier : modifiers) {
            output.append(modifier + " ");
        }

        output.append(returnType + " ");

        output.append(name + " ");

        output.append("(");
        for (String parameter : parameters) {
            output.append(parameter + " ");
        }
        output.append(")");

        output.append(" {");

        indentation++;
    }

    /**
     * Writes an indented line of text to the Java source file.
     * 
     * @param text
     *            the text to write
     */
    protected void writeLine(String text) {

        indent();
        output.append(text + "\n");
    }

    /**
     * Writes a closing brace ("}") to the Java source file. This will decrease
     * the indentation level for the text.
     */
    protected void writeClosingBrace() {

        indentation--;
        indent();
        output.append("}\n");
    }

    /**
     * Inserts a number of tabs according to the current indentation level of
     * the text.
     */
    protected void indent() {

        for (int i = 0; i < indentation; i++) {
            output.append(TAB);
        }
    }
}