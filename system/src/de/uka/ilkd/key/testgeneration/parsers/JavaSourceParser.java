package de.uka.ilkd.key.testgeneration.parsers;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

/**
 * This parser can be used in order to extract information from (and about)
 * syntactically correct Java source files. Only the public class declared in
 * the source file will be subject to the parse.
 * 
 * @author christopher
 * 
 */
public class JavaSourceParser {

    /**
     * Checks if the public class of the file declares a no-args constructor.
     * There are only two cases where this is true:
     * 
     * <pre>
     * <li>The class explicitly declares a no-args constructor</li>
     * <li>The class does not declare a constructor at all</li>
     * </pre>
     * 
     * Accordingly, this method will look for a declared no-args constructor,
     * while keeping track of parametrized constructors. If no declared no-args
     * constructor is found, the method will return true iff. the class declares
     * no other constructors.
     * 
     * @param path
     *            path to the source file
     * @return
     * @throws FileNotFoundException
     */
    public static boolean declaresNoArgsConstructor(String path)
            throws FileNotFoundException {

        // TODO: make OS agnostic
        String className = path.substring(path.lastIndexOf("/") + 1,
                path.length() - 5);

        boolean sawParametrizedConstructor = false;

        Scanner scanner = new Scanner(new File(path));

        while (scanner.hasNext()) {

            String line = scanner
                    .findInLine("public[\\s|\\n]*PrimitiveIntegerOperations\\s*\\(\\S+\\)");

            if (line != null) {
                System.out.println(line);
            }

            String next = scanner.nextLine();
        }
        return true;
    }

    public static void main(String[] args) throws FileNotFoundException {

        declaresNoArgsConstructor("/home/christopher/workspace/Key/system/test/de/uka/ilkd/key/testgeneration/targetmodels/PrimitiveIntegerOperations.java");
    }
}