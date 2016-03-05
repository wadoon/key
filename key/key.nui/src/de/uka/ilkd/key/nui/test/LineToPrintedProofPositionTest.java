package de.uka.ilkd.key.nui.test;

import static org.junit.Assert.*;

import org.junit.Test;

import de.uka.ilkd.key.java.statement.Assert;
import de.uka.ilkd.key.nui.filter.LineToPrintedProofPosition;

public class LineToPrintedProofPositionTest {

    String[] lines;

    public void init() {
        if (lines == null) {
            // one line-break between each
            lines = new String[] { "1", "22", "333", "4444", "55555" };
        }
    }

    @Test
    public void testGetLineIndex_firstLine() {
        init();
        assertEquals(0, LineToPrintedProofPosition.getLineIndex(0, lines));
        assertEquals(0, LineToPrintedProofPosition.getLineIndex(1, lines));
    }

    @Test
    public void testGetLineIndex_middleLines() {
        init();
        assertEquals(1, LineToPrintedProofPosition.getLineIndex(2, lines));
        assertEquals(1, LineToPrintedProofPosition.getLineIndex(4, lines));
        assertEquals(2, LineToPrintedProofPosition.getLineIndex(5, lines));
    }

    @Test
    public void testGetLineIndex_lastLine() {
        init();
        assertEquals(4, LineToPrintedProofPosition.getLineIndex(14, lines));
        assertEquals(4, LineToPrintedProofPosition.getLineIndex(18, lines));
    }

    @Test(expected = IndexOutOfBoundsException.class)
    public void testGetLineIndex_outOfRange_start() {
        init();
        LineToPrintedProofPosition.getLineIndex(-1, lines);
    }

    @Test(expected = IndexOutOfBoundsException.class)
    public void testGetLineIndex_outOfRange_end() {
        init();
        LineToPrintedProofPosition.getLineIndex(20, lines);
    }
    
    @Test
    public void testGetCharIndex_firstLine() {
        init();
        assertEquals(0, LineToPrintedProofPosition.getCharIndex(0, lines));
        assertEquals(2, LineToPrintedProofPosition.getCharIndex(1, lines));
    }

    @Test
    public void testGetCharIndex_middleLine() {
        init();
        assertEquals(9, LineToPrintedProofPosition.getCharIndex(3, lines));
    }

    @Test
    public void testGetCharIndex_lastLine() {
        init();
        assertEquals(14, LineToPrintedProofPosition.getCharIndex(4, lines));
    }

    @Test(expected = IndexOutOfBoundsException.class)
    public void testGetCharIndex_outOfRange_start() {
        init();
        LineToPrintedProofPosition.getCharIndex(-1, lines);
    }

    @Test(expected = IndexOutOfBoundsException.class)
    public void testGetCharIndex_outOfRange_end() {
        init();
        LineToPrintedProofPosition.getCharIndex(5, lines);
    }

    @Test
    public void testGetFirstNonWhitespace() {
        String line = "     5spaces";
        int pos = LineToPrintedProofPosition.getFirstNonWhitespace(line);
        assertEquals(pos, 5);
    }

    @Test
    public void testGetFirstNonWhitespace_emptyString() {
        String line = "";
        int pos = LineToPrintedProofPosition.getFirstNonWhitespace(line);
        assertEquals(pos, 0);
    }

    @Test
    public void testGetFirstNonWhitespace_noWhitespaces() {
        String line = "1";
        int pos = LineToPrintedProofPosition.getFirstNonWhitespace(line);
        assertEquals(pos, 0);
    }

    @Test
    public void testGetFirstNonWhitespace_justWhitespaces() {
        String line = "     ";
        int pos = LineToPrintedProofPosition.getFirstNonWhitespace(line);
        assertEquals(pos, 0);
    }

}
