package de.uka.ilkd.key.proof.io.consistency;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.nio.file.Path;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.io.RuleSource;

/**
 * Instead of directly opening an Input/OutputStream when loading source files or saving proofs, a
 * FileRepo should be used as an intermediate layer. This enables the use of various features such
 * as ensured source consistency or saving proofs as bundles (see implementations for details).
 *
 * @author Wolfram Pfeifer
 */
public interface FileRepo extends ProofDisposedListener {
    /**
     * Provides access to a file on disk.
     *
     * May return <code>null</code> if the path cannot be handled by this repository.
     * @param path the path of the file
     * @return an InputStream of the requested file, or <code>null</code>
     * @throws FileNotFoundException if the file does not exist
     * @throws IOException on IO errors, e.g. if the user has no permission to read the file
     */
    InputStream getInputStream(Path path) throws IOException;

    /**
     * Provides access to the InputStream of a RuleSource. The file the RuleSource is read from
     * is registered to the FileRepo.
     *
     * May return <code>null</code> if the source cannot be handled by this repository.
     * @param ruleSource the RuleSource
     * @return an InputStream of the RuleSource, or <code>null</code>
     * @throws IOException on IO errors
     */
    InputStream getInputStream(RuleSource ruleSource) throws IOException;

    /**
     * Provides access to the InputStream of a file identified by an URL. The file is registered to
     * the FileRepo.
     *
     * May return <code>null</code> if the url cannot be handled by this repository.
     * @param url the URL of the file
     * @return an InputStream to the file identified by the URL, or <code>null</code>
     * @throws IOException on IO errors
     */
    InputStream getInputStream(URL url) throws IOException;

    /**
     * This method can be used to write a file that has no counterpart outside to the FileRepo. If
     * there is already a file with the same name as the given one (happens for example if the proof
     * was loaded from a bundle), it is replaced.
     * @param path the path of the file to store. The path must be relative to the base directory
     *      of the proof package.
     * @return an OutputStream to the file in the FileRepo
     * @throws IOException if a file with the given path exists but can not be replaced for some
     *                     reason
     */
    OutputStream createOutputStream(Path path) throws IOException;

    /**
     * Register the proof in the FileRepo.
     * @param proof the proof to register
     */
    void registerProof(Proof proof);

    /**
     * Sets the bootclasspath (containing available classes from the Java Class Library).
     * @param path the bootclasspath to set (the method does nothing if null is given)
     * @throws IllegalStateException if the java path is already set
     */
    void setBootClassPath(File path) throws IllegalStateException;

    default boolean isBootClassPathSet() {
        return false;
    }

    /**
     * Sets the classpath.
     * @param classPath the classpath to set (the method does nothing if null is given)
     * @throws IllegalStateException if the java path is already set
     */
    void setClassPath(List<File> classPath) throws IllegalStateException;

    default boolean isClassPathSet() {
        return false;
    }

    /**
     * Sets the java path (where the source files are located).
     * @param javaPath the java path to set (the method does nothing if null is given)
     * @throws IllegalStateException if the java path is already set
     */
    void setJavaPath(String javaPath) throws IllegalStateException;

    default boolean isJavaPathSet() {
        return false;
    }

    /**
     * Sets the base directory of the proof, i.e. the main directory where the proof is loaded from.
     * When loading Java sources this is the directory the loaded file resides in.
     * When loading .key-Files this is the directory specified via "\\javaSource" or the directory
     * of the .key-File, if no source directory is specified.
     *
     * This is needed by the FileRepo for resolving pathnames.
     *
     * @param path The path of the base directory. If a file is given, then its parent directory is
     *             set as base path.
     */
    void setBaseDir(Path path);
}
