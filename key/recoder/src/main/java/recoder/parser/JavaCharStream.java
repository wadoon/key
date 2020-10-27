package recoder.parser;

import java.io.*;

public class JavaCharStream {
    public static final boolean staticFlag = true;
    public static int bufpos = -1;
    protected static int[] bufline;
    protected static int[] bufcolumn;
    protected static int column = 0;
    protected static int line = 1;
    protected static boolean prevCharIsCR = false;
    protected static boolean prevCharIsLF = false;
    protected static Reader inputStream;
    protected static char[] nextCharBuf;
    protected static char[] buffer;
    protected static int maxNextCharInd = 0;
    protected static int nextCharInd = -1;
    protected static int inBuf = 0;
    protected static int tabSize = 8;
    static int bufsize;
    static int available;
    static int tokenBegin;

    public JavaCharStream(Reader dstream, int startline, int startcolumn, int buffersize) {
        if (inputStream != null)
            throw new Error("\n   ERROR: Second call to the constructor of a static JavaCharStream.  You must\n       either use ReInit() or set the JavaCC option STATIC to false\n       during the generation of this class.");
        inputStream = dstream;
        line = startline;
        column = startcolumn - 1;
        available = bufsize = buffersize;
        buffer = new char[buffersize];
        bufline = new int[buffersize];
        bufcolumn = new int[buffersize];
        nextCharBuf = new char[4096];
    }

    public JavaCharStream(Reader dstream, int startline, int startcolumn) {
        this(dstream, startline, startcolumn, 4096);
    }

    public JavaCharStream(Reader dstream) {
        this(dstream, 1, 1, 4096);
    }

    public JavaCharStream(InputStream dstream, String encoding, int startline, int startcolumn, int buffersize) throws UnsupportedEncodingException {
        this((encoding == null) ? new InputStreamReader(dstream) : new InputStreamReader(dstream, encoding), startline, startcolumn, buffersize);
    }

    public JavaCharStream(InputStream dstream, int startline, int startcolumn, int buffersize) {
        this(new InputStreamReader(dstream), startline, startcolumn, 4096);
    }

    public JavaCharStream(InputStream dstream, String encoding, int startline, int startcolumn) throws UnsupportedEncodingException {
        this(dstream, encoding, startline, startcolumn, 4096);
    }

    public JavaCharStream(InputStream dstream, int startline, int startcolumn) {
        this(dstream, startline, startcolumn, 4096);
    }

    public JavaCharStream(InputStream dstream, String encoding) throws UnsupportedEncodingException {
        this(dstream, encoding, 1, 1, 4096);
    }

    public JavaCharStream(InputStream dstream) {
        this(dstream, 1, 1, 4096);
    }

    static final int hexval(char c) throws IOException {
        switch (c) {
            case '0':
                return 0;
            case '1':
                return 1;
            case '2':
                return 2;
            case '3':
                return 3;
            case '4':
                return 4;
            case '5':
                return 5;
            case '6':
                return 6;
            case '7':
                return 7;
            case '8':
                return 8;
            case '9':
                return 9;
            case 'A':
            case 'a':
                return 10;
            case 'B':
            case 'b':
                return 11;
            case 'C':
            case 'c':
                return 12;
            case 'D':
            case 'd':
                return 13;
            case 'E':
            case 'e':
                return 14;
            case 'F':
            case 'f':
                return 15;
        }
        throw new IOException();
    }

    protected static void setTabSize(int i) {
        tabSize = i;
    }

    protected static int getTabSize(int i) {
        return tabSize;
    }

    protected static void ExpandBuff(boolean wrapAround) {
        char[] newbuffer = new char[bufsize + 2048];
        int[] newbufline = new int[bufsize + 2048];
        int[] newbufcolumn = new int[bufsize + 2048];
        try {
            if (wrapAround) {
                System.arraycopy(buffer, tokenBegin, newbuffer, 0, bufsize - tokenBegin);
                System.arraycopy(buffer, 0, newbuffer, bufsize - tokenBegin, bufpos);
                buffer = newbuffer;
                System.arraycopy(bufline, tokenBegin, newbufline, 0, bufsize - tokenBegin);
                System.arraycopy(bufline, 0, newbufline, bufsize - tokenBegin, bufpos);
                bufline = newbufline;
                System.arraycopy(bufcolumn, tokenBegin, newbufcolumn, 0, bufsize - tokenBegin);
                System.arraycopy(bufcolumn, 0, newbufcolumn, bufsize - tokenBegin, bufpos);
                bufcolumn = newbufcolumn;
                bufpos += bufsize - tokenBegin;
            } else {
                System.arraycopy(buffer, tokenBegin, newbuffer, 0, bufsize - tokenBegin);
                buffer = newbuffer;
                System.arraycopy(bufline, tokenBegin, newbufline, 0, bufsize - tokenBegin);
                bufline = newbufline;
                System.arraycopy(bufcolumn, tokenBegin, newbufcolumn, 0, bufsize - tokenBegin);
                bufcolumn = newbufcolumn;
                bufpos -= tokenBegin;
            }
        } catch (Throwable t) {
            throw new Error(t.getMessage());
        }
        available = bufsize += 2048;
        tokenBegin = 0;
    }

    protected static void FillBuff() throws IOException {
        if (maxNextCharInd == 4096)
            maxNextCharInd = nextCharInd = 0;
        try {
            int i;
            if ((i = inputStream.read(nextCharBuf, maxNextCharInd, 4096 - maxNextCharInd)) == -1) {
                inputStream.close();
                throw new IOException();
            }
            maxNextCharInd += i;
            return;
        } catch (IOException e) {
            if (bufpos != 0) {
                bufpos--;
                backup(0);
            } else {
                bufline[bufpos] = line;
                bufcolumn[bufpos] = column;
            }
            throw e;
        }
    }

    protected static char ReadByte() throws IOException {
        if (++nextCharInd >= maxNextCharInd)
            FillBuff();
        return nextCharBuf[nextCharInd];
    }

    public static char BeginToken() throws IOException {
        if (inBuf > 0) {
            inBuf--;
            if (++bufpos == bufsize)
                bufpos = 0;
            tokenBegin = bufpos;
            return buffer[bufpos];
        }
        tokenBegin = 0;
        bufpos = -1;
        return readChar();
    }

    protected static void AdjustBuffSize() {
        if (available == bufsize) {
            if (tokenBegin > 2048) {
                bufpos = 0;
                available = tokenBegin;
            } else {
                ExpandBuff(false);
            }
        } else if (available > tokenBegin) {
            available = bufsize;
        } else if (tokenBegin - available < 2048) {
            ExpandBuff(true);
        } else {
            available = tokenBegin;
        }
    }

    protected static void UpdateLineColumn(char c) {
        column++;
        if (prevCharIsLF) {
            prevCharIsLF = false;
            line += column = 1;
        } else if (prevCharIsCR) {
            prevCharIsCR = false;
            if (c == '\n') {
                prevCharIsLF = true;
            } else {
                line += column = 1;
            }
        }
        switch (c) {
            case '\r':
                prevCharIsCR = true;
                break;
            case '\n':
                prevCharIsLF = true;
                break;
            case '\t':
                column--;
                column += tabSize - column % tabSize;
                break;
        }
        bufline[bufpos] = line;
        bufcolumn[bufpos] = column;
    }

    public static char readChar() throws IOException {
        if (inBuf > 0) {
            inBuf--;
            if (++bufpos == bufsize)
                bufpos = 0;
            return buffer[bufpos];
        }
        if (++bufpos == available)
            AdjustBuffSize();
        char c = ReadByte();
        if ((c = ReadByte()) == '\\') {
            UpdateLineColumn(c);
            int backSlashCnt = 1;
            while (true) {
                if (++bufpos == available)
                    AdjustBuffSize();
                try {
                    buffer[bufpos] = c = ReadByte();
                    if ((c = ReadByte()) != '\\') {
                        UpdateLineColumn(c);
                        if (c == 'u' && (backSlashCnt & 0x1) == 1) {
                            if (--bufpos < 0) {
                                bufpos = bufsize - 1;
                                break;
                            }
                        } else {
                            backup(backSlashCnt);
                            return '\\';
                        }
                    } else {
                        UpdateLineColumn(c);
                        backSlashCnt++;
                        continue;
                    }
                } catch (IOException e) {
                    if (backSlashCnt > 1)
                        backup(backSlashCnt);
                    return '\\';
                }
                try {
                    break;
                } catch (IOException e) {
                    throw new Error("Invalid escape character at line " + line + " column " + column + ".");
                }
            }
            while ((c = ReadByte()) == 'u')
                column++;
            buffer[bufpos] = c = (char) (hexval(c) << 12 | hexval(ReadByte()) << 8 | hexval(ReadByte()) << 4 | hexval(ReadByte()));
            column += 4;
            if (backSlashCnt == 1)
                return c;
            backup(backSlashCnt - 1);
            return '\\';
        }
        UpdateLineColumn(c);
        return c;
    }

    public static int getColumn() {
        return bufcolumn[bufpos];
    }

    public static int getLine() {
        return bufline[bufpos];
    }

    public static int getEndColumn() {
        return bufcolumn[bufpos];
    }

    public static int getEndLine() {
        return bufline[bufpos];
    }

    public static int getBeginColumn() {
        return bufcolumn[tokenBegin];
    }

    public static int getBeginLine() {
        return bufline[tokenBegin];
    }

    public static void backup(int amount) {
        inBuf += amount;
        if ((bufpos -= amount) < 0)
            bufpos += bufsize;
    }

    public static String GetImage() {
        if (bufpos >= tokenBegin)
            return new String(buffer, tokenBegin, bufpos - tokenBegin + 1);
        return new String(buffer, tokenBegin, bufsize - tokenBegin) + new String(buffer, 0, bufpos + 1);
    }

    public static char[] GetSuffix(int len) {
        char[] ret = new char[len];
        if (bufpos + 1 >= len) {
            System.arraycopy(buffer, bufpos - len + 1, ret, 0, len);
        } else {
            System.arraycopy(buffer, bufsize - len - bufpos - 1, ret, 0, len - bufpos - 1);
            System.arraycopy(buffer, 0, ret, len - bufpos - 1, bufpos + 1);
        }
        return ret;
    }

    public static void Done() {
        nextCharBuf = null;
        buffer = null;
        bufline = null;
        bufcolumn = null;
    }

    public static void adjustBeginLineColumn(int newLine, int newCol) {
        int len, start = tokenBegin;
        if (bufpos >= tokenBegin) {
            len = bufpos - tokenBegin + inBuf + 1;
        } else {
            len = bufsize - tokenBegin + bufpos + 1 + inBuf;
        }
        int i = 0, j = 0, k = 0;
        int nextColDiff = 0, columnDiff = 0;
        while (i < len && bufline[j = start % bufsize] == bufline[k = ++start % bufsize]) {
            bufline[j] = newLine;
            nextColDiff = columnDiff + bufcolumn[k] - bufcolumn[j];
            bufcolumn[j] = newCol + columnDiff;
            columnDiff = nextColDiff;
            i++;
        }
        if (i < len) {
            bufline[j] = newLine++;
            bufcolumn[j] = newCol + columnDiff;
            while (i++ < len) {
                if (bufline[j = start % bufsize] != bufline[++start % bufsize]) {
                    bufline[j] = newLine++;
                    continue;
                }
                bufline[j] = newLine;
            }
        }
        line = bufline[j];
        column = bufcolumn[j];
    }

    public void ReInit(Reader dstream, int startline, int startcolumn, int buffersize) {
        inputStream = dstream;
        line = startline;
        column = startcolumn - 1;
        if (buffer == null || buffersize != buffer.length) {
            available = bufsize = buffersize;
            buffer = new char[buffersize];
            bufline = new int[buffersize];
            bufcolumn = new int[buffersize];
            nextCharBuf = new char[4096];
        }
        prevCharIsLF = prevCharIsCR = false;
        tokenBegin = inBuf = maxNextCharInd = 0;
        nextCharInd = bufpos = -1;
    }

    public void ReInit(Reader dstream, int startline, int startcolumn) {
        ReInit(dstream, startline, startcolumn, 4096);
    }

    public void ReInit(Reader dstream) {
        ReInit(dstream, 1, 1, 4096);
    }

    public void ReInit(InputStream dstream, String encoding, int startline, int startcolumn, int buffersize) throws UnsupportedEncodingException {
        ReInit((encoding == null) ? new InputStreamReader(dstream) : new InputStreamReader(dstream, encoding), startline, startcolumn, buffersize);
    }

    public void ReInit(InputStream dstream, int startline, int startcolumn, int buffersize) {
        ReInit(new InputStreamReader(dstream), startline, startcolumn, buffersize);
    }

    public void ReInit(InputStream dstream, String encoding, int startline, int startcolumn) throws UnsupportedEncodingException {
        ReInit(dstream, encoding, startline, startcolumn, 4096);
    }

    public void ReInit(InputStream dstream, int startline, int startcolumn) {
        ReInit(dstream, startline, startcolumn, 4096);
    }

    public void ReInit(InputStream dstream, String encoding) throws UnsupportedEncodingException {
        ReInit(dstream, encoding, 1, 1, 4096);
    }

    public void ReInit(InputStream dstream) {
        ReInit(dstream, 1, 1, 4096);
    }
}
