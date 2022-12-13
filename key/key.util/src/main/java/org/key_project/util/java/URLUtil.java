package org.key_project.util.java;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipFile;

/**
 * This class contains some utility functions for URLs and URIs.
 * @author pfeifer
 */
public class URLUtil {
    /** Pattern to parse URL scheme (capture group 1) and scheme specific part (group 2). */
    private static final Pattern URL_PATTERN =
        Pattern.compile("(^[a-zA-Z][a-zA-Z0-9+\\-.]*):(.*)");

    private URLUtil() {
    }

    /**
     * This method is the central place for parsing a URL from a String. Allowed input formats are:
     * <ul>
     * <li>from DataLocation:
     * <ul>
     * <li>URLDataLocation: URL:&lt;url&gt;</li>
     * <li>ArchiveDataLocation: ARCHIVE:&lt;filename&gt;?&lt;entry&gt;</li>
     * <li>FileDataLocation: FILE:&lt;filename&gt;</li>
     * <li>SpecDataLocation: &lt;type&gt;://&lt;location&gt;</li>
     * </ul>
     * </li>
     * <li>from URL: &lt;scheme&gt;:&lt;scheme_specific_part&gt;</li>
     * <li>from File/Path (in both cases, paths may be relative and/or not normalized!):
     * <ul>
     * <li>Unix: /a/b/c</li>
     * <li>Windows: &lt;drive_letter&gt;:\a\b\c\</li>
     * </ul>
     * </li>
     * </ul>
     * <p>
     * A NullPointerException is thrown if null is given. If the input is "", ".", or a relative
     * path in general, the path is resolved against the current working directory (see system
     * property "user.dir") consistently to the behaviour of {@link Paths#get(String, String...)}.
     *
     * @param input the String to convert
     * @return a URL if successful
     * @throws MalformedURLException if the string can not be converted to URL because of an unknown
     *                               protocol or illegal format
     */
    public static URL parseURL(final String input) throws MalformedURLException {
        if (input == null) {
            throw new NullPointerException("No URL can be created from null!");
        }

        String scheme = "";
        String schemeSpecPart = "";
        Matcher m = URL_PATTERN.matcher(input);
        if (m.matches() && m.groupCount() == 2) {
            scheme = m.group(1);
            schemeSpecPart = m.group(2);
        }
        switch (scheme) {
        case "URL":
            // schemeSpecPart actually contains a URL again
            return new URL(schemeSpecPart);
        case "ARCHIVE":
            // format: "ARCHIVE:<filename>?<itemname>"
            // extract item name and zip file
            int qmindex = schemeSpecPart.lastIndexOf('?');
            String zipName = schemeSpecPart.substring(0, qmindex);
            String itemName = schemeSpecPart.substring(qmindex + 1);

            try {
                ZipFile zip = new ZipFile(zipName);
                // use special method to ensure that path separators are correct
                return getZipEntryURI(zip, itemName).toURL();
            } catch (IOException e) {
                MalformedURLException me =
                    new MalformedURLException(input + " does not contain a valid URL");
                me.initCause(e);
                throw me;
            }
        case "FILE":
            // format: "FILE:<path>"
            Path path = Paths.get(schemeSpecPart).toAbsolutePath().normalize();
            return path.toUri().toURL();
        case "":
            // only file/path without protocol
            Path p = Paths.get(input).toAbsolutePath().normalize();
            return p.toUri().toURL();
        default:
            // may still be Windows path starting with <drive_letter>:
            if (scheme.length() == 1) {
                // TODO: Theoretically, a protocol with only a single letter is allowed.
                // This (very rare) case currently is not handled correctly.
                Path windowsPath = Paths.get(input).toAbsolutePath().normalize();
                return windowsPath.toUri().toURL();
            }
            // otherwise call URL constructor
            // if this also fails, there is an unknown protocol -> MalformedURLException
            return new URL(input);
        }
    }

    /**
     * Creates a URI (that contains a URL) pointing to the entry with the given name inside the
     * given zip file. <br>
     * <br>
     * <b>Note:</b> There is an unresolved bug in Java for JarURLs when the jar path contains a
     * directory ending with "!" ("!" should be encoded as "%21", but is not). In this case, the
     * program will crash if trying to open a resource from the url. This will not be fixed until
     * {@link java.net.URI} supports RFC 3986 (currently, as of 02-2020, it seems like there are no
     * plans for this).<br>
     * <b>Workaround:</b> Don't use directory names ending with "!".
     *
     * @param zipFile the given zip
     * @param entryName the entry path relative to the root of the zip
     * @return a zip/jar URI to the entry inside the zip
     * @throws IOException if an I/O error occurs
     */
    public static URI getZipEntryURI(ZipFile zipFile, String entryName) throws IOException {

        Path zipPath = Paths.get(zipFile.getName()).toAbsolutePath().normalize();

        // TODO: Delete these lines when migrating to newer Java version!
        // These lines are needed since there is a bug in Java (up to Java 9 b80)
        // where special characters such as spaces in URI get double encoded.
        // see https://bugs.java.com/bugdatabase/view_bug.do?bug_id=8131067
        // To make it even worse, this happens only in the part before "!/".
        // We manually build our URI to ensure the encoding is correct:
        try {
            URI zipURI = zipPath.toUri();
            URI entry = new URI(null, null, entryName, null);

            // we have to cut off the starting slash if there is one
            String entryStr = entry.toString();
            entryStr = entryStr.startsWith("/") ? entryStr.substring(1) : entryStr;

            return new URI("jar:" + zipURI + "!/" + entryStr);
        } catch (URISyntaxException e) {
            throw new IOException(e);
        }

        // TODO: This should be enough if we use a Java version newer than 9 b80!
        // try (FileSystem fs = FileSystems.newFileSystem(zipPath, null)) {
        // Path p = fs.getPath(entryName);
        // return p.toUri();
        // }
    }
}
