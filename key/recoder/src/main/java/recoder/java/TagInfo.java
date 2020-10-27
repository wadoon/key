package recoder.java;

import java.io.*;
import java.util.Enumeration;
import java.util.Properties;
import java.util.Vector;

public class TagInfo {
    private static final Enumeration EMPTY_ENUMERATION = (new Vector(0)).elements();
    String rawComment;
    String introText;
    Vector<String> tagNames;
    Properties tagValues;
    boolean analyzed;

    protected TagInfo(DocComment dc) {
        this.rawComment = dc.getText();
    }

    protected String stripCommentChars(String line) {
        String result = line.trim();
        if (result.length() > 0) {
            int left = 0;
            int right = result.length() - 1;
            if (result.charAt(left) == '/')
                left++;
            while (left <= right && result.charAt(left) == '*')
                left++;
            if (result.charAt(right) == '/')
                right--;
            while (left <= right && result.charAt(right) == '*')
                right--;
            if (left <= right) {
                result = result.substring(left, right + 1).trim();
            } else {
                result = "";
            }
        }
        return result;
    }

    protected void parseRawComment() {
        LineNumberReader lnr = new LineNumberReader(new StringReader(this.rawComment));
        String currentTag = null;
        PrintWriter pw = null;
        StringWriter sw = null;
        try {
            String line;
            while ((line = lnr.readLine()) != null) {
                line = stripCommentChars(line);
                if (line.startsWith("@")) {
                    if (this.tagNames == null) {
                        this.tagNames = new Vector<String>();
                        this.tagValues = new Properties();
                    }
                    if (pw != null)
                        if (currentTag == null) {
                            this.introText = sw.toString();
                        } else {
                            this.tagValues.put(currentTag, sw.toString());
                        }
                    sw = new StringWriter();
                    pw = new PrintWriter(sw);
                    int pos = 1;
                    while (pos < line.length() && !Character.isWhitespace(line.charAt(pos)))
                        pos++;
                    currentTag = line.substring(1, pos);
                    this.tagNames.addElement(currentTag);
                    line = line.substring(pos).trim();
                } else if (pw == null) {
                    sw = new StringWriter();
                    pw = new PrintWriter(sw);
                } else {
                    pw.println("");
                }
                pw.print(line);
            }
            if (pw != null)
                if (currentTag == null) {
                    this.introText = sw.toString();
                } else {
                    this.tagValues.put(currentTag, sw.toString());
                }
        } catch (IOException ioe) {
            ioe.printStackTrace();
        }
        this.analyzed = true;
    }

    public String getIntro() {
        if (!this.analyzed)
            parseRawComment();
        return (this.introText == null) ? "" : this.introText;
    }

    public boolean hasTags() {
        return (getTagCount() > 0);
    }

    public int getTagCount() {
        if (!this.analyzed)
            parseRawComment();
        return (this.tagNames == null) ? 0 : this.tagNames.size();
    }

    public Enumeration getTags() {
        if (!this.analyzed)
            parseRawComment();
        if (this.tagNames == null)
            return EMPTY_ENUMERATION;
        return this.tagNames.elements();
    }

    public String getTagValue(String tag) {
        String result = null;
        if (tag != null) {
            if (!this.analyzed)
                parseRawComment();
            if (this.tagValues != null)
                result = this.tagValues.getProperty(tag, null);
        }
        return result;
    }
}
