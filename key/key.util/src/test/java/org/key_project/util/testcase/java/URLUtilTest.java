package org.key_project.util.testcase.java;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.URLUtil;

import java.io.FileOutputStream;
import java.io.InputStream;
import java.net.URL;
import java.net.URLConnection;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Simple test class for the URLUtil class.
 * @author pfeifer
 */
class URLUtilTest {
    /**
     * This is a test for the method {@link URLUtil#parseURL(String)}. It tests for some strings
     * if they can be converted to URLs correctly. Note: This test creates a temporary zip file.
     *
     * @throws Exception if a string can not be converted successfully
     */
    @Test
    void testTryParseURL() throws Exception {
        // test null string -> MalformedURLException
        try {
            URL uNull = URLUtil.parseURL(null);
            fail("Expected a MalformedURLException!");
        } catch (NullPointerException e) {
            assertEquals("No URL can be created from null!", e.getMessage());
        }

        // test empty string -> URL of user working directory
        URL u0 = URLUtil.parseURL("");
        assertEquals(System.getProperty("user.dir"), Paths.get(u0.toURI()).toString());

        String tmp = System.getProperty("java.io.tmpdir");
        Path p = Paths.get(tmp, "te st.txt");

        // test simple path string without url prefix and encoding
        URL u1 = URLUtil.parseURL(p.toString());
        Assertions.assertNotNull(u1);

        // test file url string
        String correctURL = p.toUri().toURL().toString();
        URL u2 = URLUtil.parseURL(correctURL);
        Assertions.assertNotNull(u2);

        // test removal of redundant elements
        Path pRedundant = Paths.get(tmp, ".", ".", "te st.txt");
        URL uRedundant = URLUtil.parseURL(pRedundant.toString());

        // test a special format of string from antlr parser ("URL:<url_string>")
        URL parserURL = URLUtil.parseURL("URL:" + correctURL);

        assertEquals(u1, u2);
        assertEquals(u1, uRedundant);
        assertEquals(u1, parserURL);

        // test http url string
        String correctHttp = "https://www.key-project.org/KEY.cer";
        URL u3 = URLUtil.parseURL(correctHttp);
        Assertions.assertNotNull(u3);

        // write a test zip file
        byte[] b = "test content".getBytes();
        String entryName = "entry with whitespace.txt";
        Path zipP = Files.createTempFile("test with whitespace!", ".zip");
        try (FileOutputStream fos = new FileOutputStream(zipP.toFile());
             ZipOutputStream zos = new ZipOutputStream(fos)) {
            zos.putNextEntry(new ZipEntry(entryName));
            zos.write(b);
        }

        try (ZipFile zf = new ZipFile(zipP.toFile())) {
            URL entryURL = URLUtil.getZipEntryURI(zf, entryName).toURL();
            URLConnection juc = entryURL.openConnection();
            juc.setUseCaches(false);
            try (InputStream is = juc.getInputStream()) {
                Assertions.assertNotNull(is);
                // try if the file can be read correctly
                assertEquals(new String(b), IOUtil.readFrom(is));
            }

            // test reparsing jar url
            URL u4 = URLUtil.parseURL(entryURL.toString());
            Assertions.assertNotNull(u4);
            assertEquals(entryURL, u4);
        }

        // clean up temporary file
        Files.deleteIfExists(zipP);
    }
}
