package com.csvanefalk.keytestgen.util.parsers;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.MappedByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.util.Calendar;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * This parser can be used in order to extract information from (and about)
 * syntactically correct Java source files. Only the public class declared in
 * the source file will be subject to the parse.
 *
 * @author christopher
 */
public class JavaSourceParser {

    /**
     * Checks if the public class of the file declares a no-args constructor.
     * There are only two cases where this is true:
     * <p/>
     * <pre>
     * <li>The class explicitly declares a no-args constructor</li>
     * <li>The class does not declare a constructor at all</li>
     * </pre>
     * <p/>
     * Accordingly, this method will look for a declared no-args constructor,
     * while keeping track of parametrized constructors. If no declared no-args
     * constructor is found, the method will return true iff. the class declares
     * no other constructors.
     *
     * @param path path to the source file
     * @return
     * @throws IOException
     */
    public static boolean declaresNoArgsConstructor(final String path)
            throws IOException {

        final long time = Calendar.getInstance().getTimeInMillis();

        final String source = JavaSourceParser.readFile(path);

        // TODO: make OS agnostic
        final String className = path.substring(path.lastIndexOf("/") + 1,
                path.length() - 5);

        /*
         * Look for an explicitly declared no-args constructor
         */
        final Pattern consPattern = Pattern.compile("public\\s+" + className
                + "\\s*\\(\\s*\\)");
        final Matcher consMatcher = consPattern.matcher(source);
        if (consMatcher.find()) {
            return true;
        }

        // TODO:

        System.out.println(Calendar.getInstance().getTimeInMillis() - time);

        return true;
    }

    /**
     * Extracts the package declaration for a Java source file on disk, if any.
     *
     * @param path path to the file
     * @return the package declaration
     * @throws FileNotFoundException
     */
    public static String getPackageDeclaration(final File file)
            throws FileNotFoundException {

        final Scanner scanner = new Scanner(file);
        String packageDeclaration = "";
        while (scanner.hasNext()) {

            packageDeclaration = scanner.nextLine();
            if (packageDeclaration != null) {

                /*
                 * A package declaration has the form "package a.b.c", so split
                 * it and select the second part.
                 */
                return packageDeclaration.replaceAll("package|;", "").trim();
            }
        }

        return packageDeclaration;
    }

    public static String getPackageDeclaration(final String path)
            throws FileNotFoundException {

        final File file = new File(path);
        return JavaSourceParser.getPackageDeclaration(file);
    }

    public static void main(final String[] args) throws IOException {

        System.out.println(JavaSourceParser.declaresNoArgsConstructor("/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java"));
    }

    /**
     * Reads a File into a String efficiently.
     * <p/>
     * Source:
     * http://stackoverflow.com/questions/326390/how-to-create-a-java-string
     * -from-the-contents-of-a-file
     *
     * @param path
     * @return
     * @throws IOException
     */
    private static String readFile(final String path) throws IOException {
        final FileInputStream stream = new FileInputStream(new File(path));
        try {
            final FileChannel fc = stream.getChannel();
            final MappedByteBuffer bb = fc.map(FileChannel.MapMode.READ_ONLY,
                    0, fc.size());
            /* Instead of using default, pass in a decoder. */
            return Charset.defaultCharset().decode(bb).toString();
        } finally {
            stream.close();
        }
    }
}